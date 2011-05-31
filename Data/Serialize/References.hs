{-# LANGUAGE Rank2Types, BangPatterns #-}
{-# OPTIONS_GHC -Wall #-}
{- |

This module provides a way to serialize graph-like structures into
lazy 'L.ByteString's.  Graph-like structures here are structures that
may reference other locations in the resulting output.  The references
are serialized as relative byte offsets.

A simple example:

@test1 :: [Word8]
test1 =
  L.unpack $ toLazyByteString id $ do
    r \<- 'newRegion'
    l1 \<- 'label' r
    'emit' r (42 :: Word32)
    'reference' S4 LE r l1
    emit r (43 :: Word32)

test1 == [42,0,0,0,252,255,255,255,43,0,0,0]
@

-}
module Data.Serialize.References
  ( -- * Monad and ByteString construction
    BuildM, toLazyByteString,

    -- * Regions
    Region, newRegion,

    -- * Emitting Data, Labels, References
    Label, label, makeLabel, placeLabel,
    reference, reference', Size(..), sizeToBytes, ByteOrder(..),
    -- ** Words
    emitWord8, emitWord8s,
    emitWord16le, emitWord16be, emitWord16host,
    emitWord32le, emitWord32be, emitWord32host,
    emitWord64le, emitWord64be, emitWord64host,
    -- ** Ints
    emitInt8, emitInt8s,
    emitInt16le, emitInt16be, emitInt16host,
    emitInt32le, emitInt32be, emitInt32host,
    emitInt64le, emitInt64be, emitInt64host,
    -- ** ByteStrings
    emitByteString, emitLazyByteString,
    -- ** Storables
    emitStorable, emitStorableList,
    -- ** Alignment
    padTo, alignedLabel
  )
where

import Blaze.ByteString.Builder hiding ( toLazyByteString )
import Control.Applicative
import Control.Monad
import Control.Monad.ST
import Data.Array.Base
import Data.Bits ( shiftL )
import Data.Int
import Data.Monoid
import Data.Word
import Foreign.Storable
import qualified Blaze.ByteString.Builder as Blaze
import qualified Data.ByteString.Lazy as L
import qualified Data.ByteString as S
import qualified Data.IntMap as IM

-- | Monad for constructing the serialised structure.
newtype BuildM a = BuildM
  { unBuildM :: forall r. 
                IM.IntMap RegionContent
             -> NextRegion
             -> NextLabel
             -> (IM.IntMap RegionContent
                   -> NextRegion
                   -> NextLabel
                   -> a
                   -> r)
             -> r }

instance Monad BuildM where
  return a = BuildM $ \s nr nl k -> k s nr nl a
  BuildM f >>= kont = BuildM $ \s nr nl k ->
    f s nr nl (\s' nr' nl' a -> unBuildM (kont a) s' nr' nl' k)

-- TODO: Hand-written instances might be more efficient
instance Functor BuildM where fmap = liftM
instance Applicative BuildM where pure = return; (<*>) = ap

-- | A location in the data stream.
newtype Label = Label Int
  deriving (Eq, Ord)

-- | A logical section of the data stream.
newtype Region = Region { regionToInt :: Int }
  deriving (Eq, Ord)

instance Show Region where
  show (Region r) = "<region" ++ show r ++ ">"

instance Show Label where
  show (Label l) = "<label" ++ show l ++ ">"

-- | The size of a reference (1, 2, 4, or 8 bytes).
data Size = S1 | S2 | S4 | S8
  deriving (Eq, Show, Ord, Enum)

-- | Translate 'Size' into matching number of bytes.
sizeToBytes :: Size -> Int
sizeToBytes s = 1 `shiftL` fromEnum s

type NextRegion = Int
type NextLabel = Int

-- | The byte ordering to be used when serializing a reference.
data ByteOrder
  = Host  -- ^ Host byte order (and endianness)
  | LE    -- ^ Little endian
  | BE    -- ^ Big endian

data RegionContent = RegionContent
  { rcItems :: [RegionItem]  -- reversed
  , rcSize  :: {-# UNPACK #-} !Int
  }

data RegionItem
  = DataItem Builder {-# UNPACK #-} !Int
    -- ^ Some data emitted to the region and its size.
  | LabelItem Label
    -- ^ The location of a label with number of padding bytes.
  | LabelRef Label ByteOrder Size (Int -> Int)
    -- ^ A reference to a label.

emptyRegionContent :: RegionContent
emptyRegionContent =
  RegionContent { rcItems = [], rcSize = 0 }

-- | Create a new region.
newRegion :: BuildM Region
newRegion = BuildM $ \s n nl k ->
  let !n' = n + 1 in
  k (IM.insert n emptyRegionContent s) n' nl (Region n)

genLabel :: BuildM Label
genLabel = BuildM $ \s nr nl k ->
  let !nl' = nl + 1 in k s nr nl' (Label nl)

withRegion :: Region -> (RegionContent -> RegionContent) -> BuildM ()
withRegion rgn@(Region r) f = BuildM $ \s nr nl k ->
  let !s' = IM.alter do_it r s in k s' nr nl ()
 where
   do_it Nothing = error $ "Non-existing region: " ++ show rgn
   do_it (Just c) = let !c' = f c in Just c'

getRegion :: Region -> BuildM RegionContent
getRegion rgn@(Region r) = BuildM $ \s nr nl k ->
  case IM.lookup r s of
    Nothing -> error $ "Non-existing region: " ++ show rgn
    Just c -> k s nr nl c

{-# INLINE emit_ #-}
emit_ :: Region -> Builder -> Int -> BuildM ()
emit_ r bld !sz = withRegion r $ \c ->
  case rcItems c of
    DataItem b n : rest ->
      -- Join with existing item if possible
      c{ rcItems = DataItem (b `mappend` bld) (n + sz) : rest,
         rcSize = rcSize c + sz }
    items ->
      c{ rcItems = DataItem bld sz : items,
         rcSize = rcSize c + sz }

-- | Emit a single byte.
emitWord8 :: Region -> Word8 -> BuildM ()
emitWord8 r w = emit_ r (fromWord8 w) 1

-- | Emit a list of bytes.
emitWord8s :: Region -> [Word8] -> BuildM ()
emitWord8s r ws = emit_ r (fromWord8s ws) (length ws)

-- | Emit a 'Word16' in little endian format.
emitWord16le :: Region -> Word16 -> BuildM ()
emitWord16le r w = emit_ r (fromWord16le w) 2

-- | Emit a 'Word16' in big endian format.
emitWord16be :: Region -> Word16 -> BuildM ()
emitWord16be r w = emit_ r (fromWord16be w) 2

-- | Emit a 'Word16' in native host order and host endianness.
emitWord16host :: Region -> Word16 -> BuildM ()
emitWord16host r w = emit_ r (fromWord16host w) 2

-- | Emit a 'Word32' in little endian format.
emitWord32le :: Region -> Word32 -> BuildM ()
emitWord32le r w = emit_ r (fromWord32le w) 4

-- | Emit a 'Word32' in big endian format.
emitWord32be :: Region -> Word32 -> BuildM ()
emitWord32be r w = emit_ r (fromWord32be w) 4

-- | Emit a 'Word32' in native host order and host endianness.
emitWord32host :: Region -> Word32 -> BuildM ()
emitWord32host r w = emit_ r (fromWord32host w) 4

-- | Emit a 'Word64' in little endian format.
emitWord64le :: Region -> Word64 -> BuildM ()
emitWord64le r w = emit_ r (fromWord64le w) 8

-- | Emit a 'Word64' in big endian format.
emitWord64be :: Region -> Word64 -> BuildM ()
emitWord64be r w = emit_ r (fromWord64be w) 8

-- | Emit a 'Word64' in native host order and host endianness.
emitWord64host :: Region -> Word64 -> BuildM ()
emitWord64host r w = emit_ r (fromWord64host w) 8


-- | Emit a single byte.
emitInt8 :: Region -> Int8 -> BuildM ()
emitInt8 r w = emit_ r (fromInt8 w) 1

-- | Emit a list of bytes.
emitInt8s :: Region -> [Int8] -> BuildM ()
emitInt8s r ws = emit_ r (fromInt8s ws) (length ws)

-- | Emit a 'Int16' in little endian format.
emitInt16le :: Region -> Int16 -> BuildM ()
emitInt16le r w = emit_ r (fromInt16le w) 2

-- | Emit a 'Int16' in big endian format.
emitInt16be :: Region -> Int16 -> BuildM ()
emitInt16be r w = emit_ r (fromInt16be w) 2

-- | Emit a 'Int16' in native host order and host endianness.
emitInt16host :: Region -> Int16 -> BuildM ()
emitInt16host r w = emit_ r (fromInt16host w) 2

-- | Emit a 'Int32' in little endian format.
emitInt32le :: Region -> Int32 -> BuildM ()
emitInt32le r w = emit_ r (fromInt32le w) 4

-- | Emit a 'Int32' in big endian format.
emitInt32be :: Region -> Int32 -> BuildM ()
emitInt32be r w = emit_ r (fromInt32be w) 4

-- | Emit a 'Int32' in native host order and host endianness.
emitInt32host :: Region -> Int32 -> BuildM ()
emitInt32host r w = emit_ r (fromInt32host w) 4

-- | Emit a 'Int64' in little endian format.
emitInt64le :: Region -> Int64 -> BuildM ()
emitInt64le r w = emit_ r (fromInt64le w) 8

-- | Emit a 'Int64' in big endian format.
emitInt64be :: Region -> Int64 -> BuildM ()
emitInt64be r w = emit_ r (fromInt64be w) 8

-- | Emit a 'Int64' in native host order and host endianness.
emitInt64host :: Region -> Int64 -> BuildM ()
emitInt64host r w = emit_ r (fromInt64host w) 8

-- | Emit a strict 'S.ByteString'.
emitByteString :: Region -> S.ByteString -> BuildM ()
emitByteString r b = emit_ r (fromByteString b) (S.length b)

-- | Emit a lazy 'L.ByteString'.
emitLazyByteString :: Region -> L.ByteString -> BuildM ()
emitLazyByteString r b =
  emit_ r (fromLazyByteString b) (fromIntegral (L.length b))

-- | Emit an instance of 'Storable'.  Does not take into account alignment.
emitStorable :: Storable a => Region -> a -> BuildM ()
emitStorable r a = emit_ r (fromStorable a) (sizeOf a)

-- | Emit a list of 'Storable' instances.  Ignores alignment.
emitStorableList :: Storable a => Region -> [a] -> BuildM ()
emitStorableList _ [] = return ()
emitStorableList r as@(a:_) =
  emit_ r (fromStorables as) (length as * sizeOf a)

-- | Emit a label at the current location in the given region.
label :: Region -> BuildM Label
label r = do l <- makeLabel; placeLabel r l; return l

-- | Create a new label (with no location attached to it).
--
-- It is up to the user to ensure that if this label is ever used in a
-- 'reference', then the label must have been placed via 'placeLabel'.
--
-- This is intended for forward references within a region:
--
-- > example r = do
-- >  l <- makeLabel
-- >  reference S4 Host r l
-- >  ... more stuff ...
-- >  placeLabel r l
-- >  ... other stuff ...
makeLabel :: BuildM Label
makeLabel = genLabel

-- | Place a label previously created with 'makeLabel'.
--
-- This function must only be called once per label.  If the same
-- label is placed multiple times, it is undefined where references to
-- it point to.
placeLabel :: Region -> Label -> BuildM ()
placeLabel r l =
  withRegion r $ \c ->
    c{ rcItems = LabelItem l : rcItems c }

-- | Insert padding bytes into given region until its size is a
-- multiple of the expected alignment.
padTo :: Region
      -> Int -- ^ Intended alignment
      -> Word8 -- ^ Fill with these bytes.
      -> BuildM ()
padTo r align byte = do
  sz <- rcSize <$> getRegion r
  let !padding = sz `rem` align
  when (padding > 0) $
    emitWord8s r (replicate padding byte)

-- | Emit an aligned label at the current location in the region.
--
-- The label's address relative to the region start will be at a
-- multiple of the given alignment
alignedLabel :: Region -> Int -> BuildM Label
alignedLabel r align = do
  padTo r align 0
  label r  

-- | Emit a reference to the given label in the current region.
--
-- The reference will be encoded as a signed integer that specifies
-- the relative distance (in bytes) from the current location to the
-- target label.
--
-- The current location starts before the reference.  A serialised
-- reference with value @0@ therefore refers to itself.
--
-- It is up to the user to ensure that references are large enough to
-- encode the required range.  If they are not in range
-- 'toLazyByteString' will fail.
-- 
reference :: Size -- ^ The size of the reference in bytes.
          -> ByteOrder -- ^ Byte order used for encoding the reference.
          -> Region -- ^ The region in which the reference will be
                    -- emitted.
          -> Label -- ^ The target label.
          -> BuildM ()
reference sz bo r l = reference' sz bo id r l

-- | Emit a reference to the given label in the current region.
--
-- The calculated offset will be passed to the function being
-- supplied.  This can be use for example to change the unit of
-- reference from bytes to, say, words.
--
-- Say, you're generating bytecode where each instruction is a
-- multiple of 4 bytes.  Then a reference is known to be a multiple of
-- 4.  If our bytecode only uses 16 bit references then it would be
-- wasteful to store the lowest 2 bits which we know to be zero.  We
-- can implement this transformation by passing @(\`shiftR\` 2)@ as
-- the transformation function.
reference' :: Size -- ^ The size of the reference in bytes.
           -> ByteOrder -- ^ Byte order used for encoding the reference.
           -> (Int -> Int) -- ^ Offset transformation function.
           -> Region -- ^ The region in which the reference will be
                    -- emitted.
           -> Label -- ^ The target label.
           -> BuildM ()
reference' sz bo f r l =
  withRegion r $ \c ->
    c{ rcItems = LabelRef l bo sz f : rcItems c,
       rcSize = rcSize c + sizeToBytes sz }

-- | Serialise the graph into a lazy 'L.ByteString'.
toLazyByteString ::
     ([Region] -> [Region])
     -- ^ Determines the ordering of the regions.  If you pass 'id'
     -- regions will occur in creation order.
  -> BuildM ()
  -> L.ByteString
toLazyByteString order build =
  -- NOTE: We rely on the fact that the Monoid instance for Builder is
  -- lazy.
  unBuildM build IM.empty 0 0 ( \regions _nextRegion numLabels _ ->
   let ~(bytes, refs) =
        runST (do
        let regions_ordered = order (map Region (IM.keys regions))
        label_locs <- mkLabelPositions numLabels

        let
          --go :: [RegionItem] -> Int -> Builder -> [RegionContent]
          --   -> ST s (Builder, UArray Int Int)
          go [] !_ out [] = do
            arr <- unsafeFreezeSTUArray label_locs
            return (out, arr)
          go [] !sz out (rc:rcs) =
            go (reverse (rcItems rc)) sz out rcs
          go (item:items) !sz out rcs =
            case item of
              DataItem b sz' ->
                go items (sz + sz') (out `mappend` b) rcs
              LabelItem (Label l) -> do
                writeArray label_locs l sz
                go items sz out rcs
              LabelRef (Label l) bo sz' f -> do
                -- Here comes the magic.  We're referencing refs which is
                -- actually the result we're currently constructing.  This
                -- is what the mfix is for.
                let ~target = refs ! l
                --when (target == (-1)) $ 
                go items (sz + sizeToBytes sz')
                   (out `mappend`
                    writeRef bo sz' (if target /= (-1) then f (target - sz)
                                      else dangling (Label l) sz))
                   rcs
        let contents = map ((regions IM.!) . regionToInt) regions_ordered
        go [] 0 mempty contents)
        
    in Blaze.toLazyByteString bytes)
  where
   mkLabelPositions :: Int -> ST s (STUArray s Int Int)
   mkLabelPositions numLabels =
     newArray (0, numLabels - 1) (-1 :: Int)

dangling :: Label -> Int -> a
dangling l sz =
  error $ "Reference to unplaced " ++ show l ++
          " at offset " ++ show sz

writeRef :: ByteOrder -> Size -> Int -> Builder
writeRef _ S1 offs | -128 <= offs && offs <= 127 =
  fromWrite (writeInt8 (fromIntegral offs))
writeRef bo S2 offs | -32768 <= offs && offs <= 32767 =
  case bo of
    LE -> fromWrite (writeInt16le (fromIntegral offs))
    BE -> fromWrite (writeInt16be (fromIntegral offs))
    Host -> fromWrite (writeInt16host (fromIntegral offs))
writeRef bo S4 offs = -- it's probably in range
  case bo of
    LE -> fromWrite (writeInt32le (fromIntegral offs))
    BE -> fromWrite (writeInt32be (fromIntegral offs))
    Host -> fromWrite (writeInt32host (fromIntegral offs))
writeRef bo S8 offs =
  case bo of
    LE -> fromWrite (writeInt64le (fromIntegral offs))
    BE -> fromWrite (writeInt64be (fromIntegral offs))
    Host -> fromWrite (writeInt64host (fromIntegral offs))
writeRef _ s offs =
  error $ "Target (" ++ show offs ++ ") out ouf range for size " ++ show s

{-
test1 :: [Word8]
test1 =
  L.unpack $ toLazyByteString id $ do
    r <- newRegion
    l1 <- label r
    emit r (42 :: Word32)
    reference S4 LE r l1
    emit r (43 :: Word32)

test2 :: [Word8]
test2 =
  L.unpack $ toLazyByteString id $ do
    r <- newRegion
    l1 <- makeLabel
    emit r (42 :: Word32)
    reference S4 LE r l1
    emit r (43 :: Word32)
    placeLabel r l1
-}