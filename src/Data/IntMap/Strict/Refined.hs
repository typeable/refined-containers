-- | This module defines a way to prove that a key exists in a map, so that the
-- key can be used to index into the map without using a 'Maybe', or manually
-- handling the \"impossible\" case with 'error' or other partial functions.
--
-- To do this, @'IntMap' s v@ has a type parameter @s@ that identifies its set
-- of keys, so that if another map has the same type parameter, you know that
-- map has the same set of keys. There is @'Key' s@, a type of keys that have
-- been validated to belong to the set identified by @s@, and for which the
-- operation of indexing into a @'IntMap' s v@ (only for the same @s@) can
-- proceed without failure (see '!'). The type @s@ itself has no internal
-- structure, rather it is merely a skolem type variable (rank-2 polymorphism
-- 'Control.Monad.ST.runST' trick) introduced by "Data.Reflection".
--
-- Like "Data.IntMap.Strict", functions in this module are strict in the keys
-- and values. The "Data.IntMap.Refined" module reuses the same 'IntMap' type
-- but provides functions that operate lazily on the values.
module Data.IntMap.Strict.Refined
  (
  -- * Map type
    Common.IntMap
  , Common.Key
  -- * Existentials and common proofs
  , Common.SomeIntMap(..)
  , Common.withIntMap
  , Common.SomeIntMapWith(..)
  , Common.withIntMapWith
  , Common.Some2IntMapWith(..)
  , Common.with2IntMapWith
  , SupersetProof(..)
  , EmptyProof(..)
  -- * Construction
  , Common.empty
  , singleton
  , SingletonProof(..)
  , fromSet
  , Common.fromIntMap
  , fromTraversableWithKey
  , FromTraversableProof(..)
  -- * Insertion
  , insert
  , InsertProof(..)
  , reinsert
  , insertLookupWithKey
  -- * Deletion/Update
  , Common.delete
  , adjust
  , adjustWithKey
  , update
  , updateLookupWithKey
  -- * Query
  , Common.lookup
  , (Common.!)
  , Common.member
  , Common.lookupLT
  , Common.lookupGT
  , Common.lookupLE
  , Common.lookupGE
  , Common.null
  , Common.isSubmapOfBy
  , SubsetProof(..)
  , Common.disjoint
  , DisjointProof(..)
  -- * Combine
  , zipWithKey
  , bind
  , unionWithKey
  , UnionProof(..)
  , Common.difference
  , DifferenceProof(..)
  , differenceWithKey
  , PartialDifferenceProof(..)
  , intersectionWithKey
  , IntersectionProof(..)
  -- * Traversal
  , mapWithKey
  , traverseWithKey
  , mapAccumLWithKey
  , mapAccumRWithKey
  , mapKeysWith
  , MapProof(..)
  , backpermuteKeys
  -- * Folds
  , Common.foldMapWithKey
  , Common.foldrWithKey
  , Common.foldlWithKey
  , Common.foldrWithKey'
  , Common.foldlWithKey'
  -- * Conversion
  , Common.toIntMap
  , Common.keysSet
  , Common.toList
  , Common.toDescList
  -- * Filter
  , Common.restrictKeys
  , Common.withoutKeys
  , Common.filterWithKey
  , Common.partitionWithKey
  , PartitionProof(..)
  , Common.spanAntitone
  , PartialPartitionProof(..)
  , mapMaybeWithKey
  , mapEitherWithKey
  , Common.splitLookup
  , SplitProof(..)
  -- * Min/Max
  , updateMinWithKey
  , updateMaxWithKey
  , adjustMinWithKey
  , adjustMaxWithKey
  , Common.minViewWithKey
  , Common.maxViewWithKey
  -- * Casts
  , Common.castKey
  , Common.cast
  , castFlavor
  ) where

import           Data.Coerce
import           Data.Container.Refined.Proofs
import           Data.Container.Refined.Unsafe
import           Data.Functor
import qualified Data.IntMap.Strict as IntMap
import           Data.IntMap.Common.Refined
  ( IntMap(..), Key, unsafeCastKey, unsafeKey, SomeIntMapWith(..)
  , Some2IntMapWith(..), (!)
  )
import qualified Data.IntMap.Common.Refined as Common
import           Data.Proxy
import           Data.Reflection
import           Data.Traversable
import           Data.Type.Coercion
import           Prelude hiding (lookup, null)
import           Refined
import           Refined.Unsafe


-- | Create a map with a single key-value pair, and return a proof that the
-- key is in the resulting map.
singleton :: forall a. Int -> a -> SomeIntMapWith (SingletonProof 'Int Int) a
singleton k v = SomeIntMapWith (IntMap $ IntMap.singleton k v)
  $ SingletonProof (unsafeKey k)

-- | Create a map from a set of keys, and a function that for each key computes
-- the corresponding value.
fromSet :: forall s a. KnownIntSet s => (Key s -> a) -> IntMap s a
fromSet f = IntMap $ IntMap.fromSet (f . unsafeKey) (reflect $ Proxy @s)

-- | Create a map from an arbitrary traversable of key-value pairs.
fromTraversableWithKey
  :: forall t a. Traversable t
  => (Int -> a -> a -> a)
  -> t (Int, a)
  -> SomeIntMapWith (FromTraversableProof 'Int t Int) a
fromTraversableWithKey f xs = SomeIntMapWith (IntMap m)
  $ FromTraversableProof proof
  where
    (m, proof) = mapAccumL
      (\s (k, v) -> (IntMap.insertWithKey f k v s, unsafeKey k))
      IntMap.empty
      xs

-- | Insert a key-value pair into the map to obtain a potentially larger map,
-- guaranteed to contain the given key. If the key was already present, the
-- associated value is replaced with the supplied value.
insert
  :: forall s a. Int
  -> a
  -> IntMap s a
  -> SomeIntMapWith (InsertProof 'Int Int s) a
insert k v (IntMap m) = SomeIntMapWith (IntMap $ IntMap.insert k v m)
  $ InsertProof (unsafeKey k) unsafeSubset

-- | Overwrite a key-value pair that is known to already be in the map. The set
-- of keys remains the same.
reinsert
  :: forall s a. Key s -> a -> IntMap s a -> IntMap s a
reinsert = gcoerceWith (unsafeCastKey @s) $ coerce $ IntMap.insert @a

-- | Insert a key-value pair into the map using a combining function, and if
-- the key was already present, the old value is returned along with the proof
-- that the key was present.
insertLookupWithKey
  :: forall s a. (Key s -> a -> a -> a)
  -> Int
  -> a
  -> IntMap s a
  -> (Maybe (Key s, a), SomeIntMapWith (InsertProof 'Int Int s) a)
insertLookupWithKey f k v (IntMap m)
  = case IntMap.insertLookupWithKey (f . unsafeKey) k v m of
    (v', !m') -> ((unsafeKey k,) <$> v',)
      $ SomeIntMapWith (IntMap m') $ InsertProof (unsafeKey k) unsafeSubset

-- | Update the value at a specific key known the be in the map using the given
-- function. The set of keys remains the same.
adjust :: forall s a. (a -> a) -> Key s -> IntMap s a -> IntMap s a
adjust = gcoerceWith (unsafeCastKey @s) $ coerce $ IntMap.adjust @a

-- | If the given key is in the map, update the associated value using the given
-- function with a proof that the key was in the map; otherwise return the map
-- unchanged. In any case the set of keys remains the same.
adjustWithKey
  :: forall s a. (Key s -> a -> a) -> Int -> IntMap s a -> IntMap s a
adjustWithKey = gcoerceWith (unsafeCastKey @s) $ coerce
  $ IntMap.adjustWithKey @a

-- | Update or delete a key known to be in the map using the given function,
-- returning a potentially smaller map.
update
  :: forall s a. (a -> Maybe a)
  -> Key s
  -> IntMap s a
  -> SomeIntMapWith (SupersetProof 'Int s) a
update f k (IntMap m) = SomeIntMapWith (IntMap $ IntMap.update f (unrefine k) m)
  $ SupersetProof unsafeSubset

-- | If the given key is in the map, update or delete it using the given
-- function with a proof that the key was in the map; otherwise the map is
-- unchanged. Alongside return the new value if it was updated, or the old value
-- if it was deleted, and a proof that the key was in the map.
updateLookupWithKey
  :: forall s a. (Key s -> a -> Maybe a)
  -> Int
  -> IntMap s a
  -> (Maybe (Key s, a), SomeIntMapWith (SupersetProof 'Int s) a)
updateLookupWithKey f k (IntMap m)
  = case IntMap.updateLookupWithKey (f . unsafeKey) k m of
    (v', !m') -> ((unsafeKey k,) <$> v',)
      $ SomeIntMapWith (IntMap m') $ SupersetProof unsafeSubset

-- | Given two maps proven to have the same keys, for each key apply the
-- function to the associated values, to obtain a new map with the same keys.
zipWithKey
  :: forall s a b c. (Key s -> a -> b -> c)
  -> IntMap s a
  -> IntMap s b
  -> IntMap s c
zipWithKey f (IntMap m1) (IntMap m2) = IntMap
  $ IntMap.mergeWithKey (\k x y -> Just $ f (unsafeKey k) x y)
    (\m -> if IntMap.null m
      then IntMap.empty
      else
        error "zipWithKey: bug: Data.IntMap.Strict.Refined has been subverted")
    (\m -> if IntMap.null m
      then IntMap.empty
      else
        error "zipWithKey: bug: Data.IntMap.Strict.Refined has been subverted")
    --  ^ Work around https://github.com/haskell/containers/issues/979
    m1
    m2

-- | Return the union of two maps, with a given combining function for keys that
-- exist in both maps simultaneously.
--
-- You can use 'andLeft' and 'andRight' to obtain @'Key' s@ and @'Key' t@
-- respectively.
unionWithKey
  :: forall s t a. (Refined (InSet 'Int s && InSet 'Int t) Int -> a -> a -> a)
  -> IntMap s a
  -> IntMap t a
  -> SomeIntMapWith (UnionProof 'Int s t) a
unionWithKey f (IntMap m1) (IntMap m2)
  = SomeIntMapWith (IntMap $ IntMap.unionWithKey (f . reallyUnsafeRefine) m1 m2)
    $ UnionProof unsafeSubset unsafeSubsetWith2

-- | For keys that appear in both maps, the given function decides whether the
-- key is removed from the first map.
--
-- You can use 'andLeft' and 'andRight' to obtain @'Key' s@ and @'Key' t@
-- respectively.
differenceWithKey
  :: forall s t a b. (Refined (InSet 'Int s && InSet 'Int t) Int
    -> a
    -> b
    -> Maybe a)
  -> IntMap s a
  -> IntMap t b
  -> SomeIntMapWith (PartialDifferenceProof 'Int s t) a
differenceWithKey f (IntMap m1) (IntMap m2) = SomeIntMapWith
  (IntMap $ IntMap.differenceWithKey (f . reallyUnsafeRefine) m1 m2)
  $ PartialDifferenceProof unsafeSubset unsafeSubset

-- | Return the intersection of two maps with the given combining function.
--
-- You can use 'andLeft' and 'andRight' to obtain @'Key' s@ and @'Key' t@
-- respectively.
intersectionWithKey
  :: forall s t a b c. (Refined (InSet 'Int s && InSet 'Int t) Int
    -> a
    -> b
    -> c)
  -> IntMap s a
  -> IntMap t b
  -> SomeIntMapWith (IntersectionProof 'Int s t) c
intersectionWithKey f (IntMap m1) (IntMap m2) = SomeIntMapWith
  (IntMap $ IntMap.intersectionWithKey (f . reallyUnsafeRefine) m1 m2)
  $ IntersectionProof unsafeSubset unsafeSubsetWith2

-- | Apply a function to all values in a map, together with their corresponding
-- keys, that are proven to be in the map. The set of keys remains the same.
mapWithKey :: forall s a b. (Key s -> a -> b) -> IntMap s a -> IntMap s b
mapWithKey = gcoerceWith (unsafeCastKey @s) $ coerce $ IntMap.mapWithKey @a @b

-- | Map an 'Applicative' transformation in ascending order of keys, with access
-- to each value's corresponding key and a proof that it is in the map. The set
-- of keys remains unchanged.
traverseWithKey
  :: forall s f a b. Applicative f
  => (Key s -> a -> f b) -> IntMap s a -> f (IntMap s b)
traverseWithKey f (IntMap m)
  = IntMap <$> IntMap.traverseWithKey (f . unsafeKey) m

-- | Thread an accumularing argument through the map in ascending order of keys.
mapAccumLWithKey
  :: forall s a b c. (a -> Key s -> b -> (a, c))
  -> a
  -> IntMap s b
  -> (a, IntMap s c)
mapAccumLWithKey = gcoerceWith (unsafeCastKey @s) $ coerce
  $ IntMap.mapAccumWithKey @a @b @c

-- | Thread an accumularing argument through the map in descending order of
-- keys.
mapAccumRWithKey
  :: forall s a b c. (a -> Key s -> b -> (a, c))
  -> a
  -> IntMap s b
  -> (a, IntMap s c)
mapAccumRWithKey = gcoerceWith (unsafeCastKey @s) $ coerce
  $ IntMap.mapAccumRWithKey @a @b @c

-- | @'mapKeysWith' c f m@ applies @f@ to each key of @m@ and collects the
-- results into a new map. For keys that were mapped to the same new key, @c@
-- acts as the combining function for corresponding values.
mapKeysWith
  :: forall s a. (a -> a -> a)
  -> (Key s -> Int)
  -> IntMap s a
  -> SomeIntMapWith (MapProof 'Int s Int Int) a
mapKeysWith f g (IntMap m)
  = SomeIntMapWith (IntMap $ IntMap.mapKeysWith f (g . unsafeKey) m)
    $ MapProof (unsafeKey . g) \k2 ->
      case IntMap.lookup (unrefine k2) backMap of
        Nothing -> error
          "mapKeysWith: bug: Data.IntMap.Strict.Refined has been subverted"
        Just k1 -> k1
  where
    ~backMap = IntMap.fromList
      [ (k2, unsafeKey k1)
      | k1 <- IntMap.keys m
      , let !k2 = g $ unsafeKey k1
      ]

-- | Apply a function to all values in a map, together with their corresponding
-- keys, and collect only the 'Just' results, returning a potentially smaller
-- map.
mapMaybeWithKey
  :: forall s a b. (Key s -> a -> Maybe b)
  -> IntMap s a
  -> SomeIntMapWith (SupersetProof 'Int s) b
mapMaybeWithKey f (IntMap m)
  = SomeIntMapWith (IntMap $ IntMap.mapMaybeWithKey (f . unsafeKey) m)
    $ SupersetProof unsafeSubset

-- | Apply a function to all values in a map, together with their corresponding
-- keys, and collect the 'Left' and 'Right' results into separate (disjoint)
-- maps.
mapEitherWithKey
  :: forall s a b c. (Key s -> a -> Either b c)
  -> IntMap s a
  -> Some2IntMapWith (PartitionProof 'Int s Int) b c
mapEitherWithKey p (IntMap m)
  = case IntMap.mapEitherWithKey (p . unsafeKey) m of
    (m1, m2) -> Some2IntMapWith (IntMap m1) (IntMap m2) $ PartitionProof
      do \k -> case IntMap.lookup (unrefine k) m of
          Nothing -> error
            "mapEitherWithKey: bug: Data.IntMap.Strict.Refined has been subverted"
          Just x -> case p k x of
            Left _ -> Left $ unsafeKey $ unrefine k
            Right _ -> Right $ unsafeKey $ unrefine k
      unsafeSubset unsafeSubsetWith2 \f g -> unsafeSubsetWith2 f g

-- | Update or delete the value at the smallest key, returning a potentially
-- smaller map.
updateMinWithKey
  :: forall s a. (Key s -> a -> Maybe a)
  -> IntMap s a
  -> SomeIntMapWith (SupersetProof 'Int s) a
updateMinWithKey f (IntMap m)
  = SomeIntMapWith (IntMap $ IntMap.updateMinWithKey (f . unsafeKey) m)
    $ SupersetProof unsafeSubset

-- | Update or delete the value at the largest key, returning a potentially
-- smaller map.
updateMaxWithKey
  :: forall s a. (Key s -> a -> Maybe a)
  -> IntMap s a
  -> SomeIntMapWith (SupersetProof 'Int s) a
updateMaxWithKey f (IntMap m)
  = SomeIntMapWith (IntMap $ IntMap.updateMaxWithKey (f . unsafeKey) m)
    $ SupersetProof unsafeSubset

-- | Adjust the value at the smallest key. The set of keys remains unchanged.
adjustMinWithKey :: forall s a. (Key s -> a -> a) -> IntMap s a -> IntMap s a
adjustMinWithKey f (IntMap m)
  = IntMap $ IntMap.updateMinWithKey ((Just .) . f . unsafeKey) m

-- | Adjust the value at the greatest key. The set of keys remains unchanged.
adjustMaxWithKey :: forall s a. (Key s -> a -> a) -> IntMap s a -> IntMap s a
adjustMaxWithKey f (IntMap m)
  = IntMap $ IntMap.updateMaxWithKey ((Just .) . f . unsafeKey) m

-- | @'bind' m f@ is a map that for each key @k :: 'Key' s@, contains the
-- value @f (m '!' k) '!' k@, similar to @'>>='@ for functions.
bind :: forall s a b. IntMap s a -> (a -> IntMap s b) -> IntMap s b
bind m f = mapWithKey (\k x -> f x ! k) m

-- | Apply the inverse image of the given function to the keys of the given map,
-- so that for all @k :: 'Key' s2@,
-- @'backpermuteKeys' f m '!' k = m '!' f k@.
--
-- If maps are identified with functions, this computes the composition.
backpermuteKeys
  :: forall s1 s2 a. KnownIntSet s2
  => (Key s2 -> Key s1) -> IntMap s1 a -> IntMap s2 a
backpermuteKeys f m = fromSet \k -> m ! f k
