-- | This module defines a way to prove that a key exists in a map, so that the
-- key can be used to index into the map without using a 'Maybe', or manually
-- handling the \"impossible\" case with 'error' or other partial functions.
--
-- To do this, @'HashMap' s k v@ has a type parameter @s@ that identifies its
-- set of keys, so that if another map has the same type parameter, you know
-- that map has the same set of keys. There is @'Key' s k@, a type of keys that
-- have been validated to belong to the set identified by @s@, and for which the
-- operation of indexing into a @'HashMap' s k v@ (only for the same @s@) can
-- proceed without failure (see '!'). The type @s@ itself has no internal
-- structure, rather it is merely a skolem type variable (rank-2 polymorphism
-- 'Control.Monad.ST.runST' trick) introduced by "Data.Reflection".
--
-- Like "Data.HashMap.Strict", functions in this module are strict in the keys
-- and values. The "Data.HashMap.Refined" module reuses the same 'HashMap' type
-- but provides functions that operate lazily on the values.
--
-- = Warning
-- This module together with "Data.HashMap.Lazy" rely on 'Eq' and 'Hashable'
-- instances being lawful: that '==' is an equivalence relation, and that
-- 'Data.Hashable.hashWithSalt' is defined on the quotient by this equivalence
-- relation; at least for the subset of values that are actually encountered at
-- runtime. If this assumption is violated, this module may not be able to
-- uphold its invariants and may throw errors. In particular beware of NaN in
-- 'Float' and 'Double', and, if using @hashable < 1.3@, beware of @0@ and @-0@.
module Data.HashMap.Strict.Refined
  (
  -- * Map type
    Common.HashMap
  , Common.Key
  -- * Existentials and common proofs
  , Common.SomeHashMap(..)
  , Common.withHashMap
  , Common.SomeHashMapWith(..)
  , Common.withHashMapWith
  , Common.Some2HashMapWith(..)
  , Common.with2HashMapWith
  , SupersetProof(..)
  , EmptyProof(..)
  -- * Construction
  , Common.empty
  , singleton
  , SingletonProof(..)
  , fromSet
  , Common.fromHashMap
  , Common.verifyHashMap
  , fromTraversable
  , fromTraversableWith
  , fromTraversableWithKey
  , FromTraversableProof(..)
  -- * Insertion
  , insert
  , insertWith
  , insertWithKey
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
  , Common.toMap
  , Common.keysSet
  , Common.toList
  -- * Filter
  , Common.restrictKeys
  , Common.withoutKeys
  , Common.filterWithKey
  , Common.partitionWithKey
  , PartitionProof(..)
  , mapMaybeWithKey
  , mapEitherWithKey
  -- * Casts
  , Common.castKey
  , Common.cast
  , castFlavor
  ) where

import           Data.Coerce
import           Data.Container.Refined.Hashable
import           Data.Container.Refined.Proofs
import           Data.Container.Refined.Unsafe
import           Data.Functor
import qualified Data.HashMap.Strict as HashMap
import           Data.HashMap.Common.Refined
  ( HashMap(..), Key, unsafeCastKey, unsafeKey, SomeHashMapWith(..)
  , Some2HashMapWith(..), (!)
  )
import qualified Data.HashMap.Common.Refined as Common
import qualified Data.HashSet as HashSet
import           Data.Proxy
import           Data.Reflection
import           Data.Traversable
import           Data.Traversable.WithIndex
import           Data.Type.Coercion
import           Prelude hiding (lookup, null)
import           Refined
import           Refined.Unsafe


-- | Create a map with a single key-value pair, and return a proof that the
-- key is in the resulting map.
singleton
  :: forall k a. Hashable k
  => k -> a -> SomeHashMapWith (SingletonProof 'Hashed k) k a
singleton k v = SomeHashMapWith (HashMap $ HashMap.singleton k v)
  $ SingletonProof (unsafeKey k)

-- | Create a map from a set of keys, and a function that for each key computes
-- the corresponding value.
fromSet :: forall s k a. KnownHashSet s k => (Key s k -> a) -> HashMap s k a
fromSet f = HashMap $ HashMap.mapWithKey (\k _ -> f $ unsafeKey k)
  $ HashSet.toMap (reflect $ Proxy @s)

-- | Create a map from an arbitrary traversable of key-value pairs. If a key is
-- repeated, the retained value is the last one in traversal order. If you're
-- looking for @fromList@, this is the function you want.
fromTraversable
  :: forall t k a. (Traversable t, Hashable k)
  => t (k, a) -> SomeHashMapWith (FromTraversableProof 'Hashed t k) k a
fromTraversable xs = SomeHashMapWith (HashMap m) $ FromTraversableProof proof
  where
    (m, proof) = mapAccumL
      (\s (k, v) -> let !s' = HashMap.insert k v s in (s', unsafeKey k))
      HashMap.empty
      xs

-- | Create a map from an arbitrary traversable of key-value pairs, with a
-- function for combining values for repeated keys. The function is called as if
-- by 'foldl1', but flipped:
--
-- @
-- 'fromTraversableWith' f [(k, x1), (k, x2), (k, x3)]
--   = 'singleton' k (f x3 (f x2 x1))
-- @
fromTraversableWith
  :: forall t k a. (Traversable t, Hashable k)
  => (a -> a -> a)
  -> t (k, a)
  -> SomeHashMapWith (FromTraversableProof 'Hashed t k) k a
fromTraversableWith f xs
  = SomeHashMapWith (HashMap m) $ FromTraversableProof proof
  where
    (m, proof) = mapAccumL
      (\s (k, v) -> let !s' = HashMap.insertWith f k v s in (s', unsafeKey k))
      HashMap.empty
      xs

-- | Create a map from an arbitrary traversable of key-value pairs. Like
-- 'fromTraversableWith', but the combining function has access to the key.
fromTraversableWithKey
  :: forall t k a. (Traversable t, Hashable k)
  => (k -> a -> a -> a)
  -> t (k, a)
  -> SomeHashMapWith (FromTraversableProof 'Hashed t k) k a
fromTraversableWithKey f xs
  = SomeHashMapWith (HashMap m) $ FromTraversableProof proof
  where
    (m, proof) = mapAccumL
      (\s (k, v)
        -> let !s' = HashMap.insertWith (f k) k v s in (s', unsafeKey k))
      HashMap.empty
      xs

-- | Insert a key-value pair into the map to obtain a potentially larger map,
-- guaranteed to contain the given key. If the key was already present, the
-- associated value is replaced with the supplied value.
insert
  :: forall s k a. Hashable k
  => k -> a -> HashMap s k a -> SomeHashMapWith (InsertProof 'Hashed k s) k a
insert k v (HashMap m) = SomeHashMapWith (HashMap $ HashMap.insert k v m)
  $ InsertProof (unsafeKey k) unsafeSubset

-- | Insert a key-value pair into the map to obtain a potentially larger map,
-- guaranteed to contain the given key. If the key was already present, the
-- supplied function is used to combine the new value with the old (in that
-- order).
insertWith
  :: forall s k a. Hashable k
  => (a -> a -> a)
  -> k
  -> a
  -> HashMap s k a
  -> SomeHashMapWith (InsertProof 'Hashed k s) k a
insertWith f k v (HashMap m) = SomeHashMapWith
  (HashMap $ HashMap.insertWith f k v m)
  $ InsertProof (unsafeKey k) unsafeSubset

-- | Insert a key-value pair into the map to obtain a potentially larger map,
-- guaranteed to contain the given key. Like 'insertWith', but the combining
-- function has access to the key, which is guaranteed to be in the old map.
insertWithKey
  :: forall s k a. Hashable k
  => (Key s k -> a -> a -> a)
  -> k
  -> a
  -> HashMap s k a
  -> SomeHashMapWith (InsertProof 'Hashed k s) k a
insertWithKey f k v (HashMap m) = SomeHashMapWith
  (HashMap $ HashMap.insertWith (f $ unsafeKey k) k v m)
  $ InsertProof (unsafeKey k) unsafeSubset

-- | Overwrite a key-value pair that is known to already be in the map. The set
-- of keys remains the same.
reinsert
  :: forall s k a. Hashable k
  => Key s k -> a -> HashMap s k a -> HashMap s k a
reinsert = gcoerceWith (unsafeCastKey @s @k) $ coerce $ HashMap.insert @k @a

-- | Insert a key-value pair into the map using a combining function, and if
-- the key was already present, the old value is returned along with the proof
-- that the key was present.
insertLookupWithKey
  :: forall s k a. Hashable k
  => (Key s k -> a -> a -> a)
  -> k
  -> a
  -> HashMap s k a
  -> (Maybe (Key s k, a), SomeHashMapWith (InsertProof 'Hashed k s) k a)
insertLookupWithKey f k v (HashMap m) =
  ( (unsafeKey k,) <$> HashMap.lookup k m
  , SomeHashMapWith (HashMap $ HashMap.insertWith (f $ unsafeKey k) k v m)
    $ InsertProof (unsafeKey k) unsafeSubset
  )

-- | Update the value at a specific key known the be in the map using the given
-- function. The set of keys remains the same.
adjust
  :: forall s k a. Hashable k
  => (a -> a) -> Key s k -> HashMap s k a -> HashMap s k a
adjust = gcoerceWith (unsafeCastKey @s @k) $ coerce $ HashMap.adjust @k @a

-- | If the given key is in the map, update the associated value using the given
-- function with a proof that the key was in the map; otherwise return the map
-- unchanged. In any case the set of keys remains the same.
adjustWithKey
  :: forall s k a. Hashable k
  => (Key s k -> a -> a) -> k -> HashMap s k a -> HashMap s k a
adjustWithKey f k (HashMap m) = HashMap $ HashMap.adjust (f $ unsafeKey k) k m

-- | Update or delete a key known to be in the map using the given function,
-- returning a potentially smaller map.
update
  :: forall s k a. Hashable k
  => (a -> Maybe a)
  -> Key s k
  -> HashMap s k a
  -> SomeHashMapWith (SupersetProof 'Hashed s) k a
update f k (HashMap m)
  = SomeHashMapWith (HashMap $ HashMap.update f (unrefine k) m)
    $ SupersetProof unsafeSubset

-- | If the given key is in the map, update or delete it using the given
-- function with a proof that the key was in the map; otherwise the map is
-- unchanged. Alongside return the new value if it was updated, or the old value
-- if it was deleted, and a proof that the key was in the map.
updateLookupWithKey
  :: forall s k a. Hashable k
  => (Key s k -> a -> Maybe a)
  -> k
  -> HashMap s k a
  -> (Maybe (Key s k, a), SomeHashMapWith (SupersetProof 'Hashed s) k a)
updateLookupWithKey f k (HashMap m) =
  ( (unsafeKey k,) <$> HashMap.lookup k m
  , SomeHashMapWith (HashMap $ HashMap.update (f $ unsafeKey k) k m)
    $ SupersetProof unsafeSubset
  )

-- | Given two maps proven to have the same keys, for each key apply the
-- function to the associated values, to obtain a new map with the same keys.
zipWithKey
  :: forall s k a b c. Hashable k
  => (Key s k -> a -> b -> c) -> HashMap s k a -> HashMap s k b -> HashMap s k c
zipWithKey = gcoerceWith (unsafeCastKey @s @k) $ coerce
  $ HashMap.intersectionWithKey @k @a @b @c

-- | Return the union of two maps, with a given combining function for keys that
-- exist in both maps simultaneously.
--
-- You can use 'andLeft' and 'andRight' to obtain @'Key' s k@ and @'Key' t k@
-- respectively.
unionWithKey
  :: forall s t k a. Hashable k
  => (Refined (InSet 'Hashed s && InSet 'Hashed t) k -> a -> a -> a)
  -> HashMap s k a
  -> HashMap t k a
  -> SomeHashMapWith (UnionProof 'Hashed s t) k a
unionWithKey f (HashMap m1) (HashMap m2) = SomeHashMapWith
  (HashMap $ HashMap.unionWithKey (f . reallyUnsafeRefine) m1 m2)
  $ UnionProof unsafeSubset unsafeSubsetWith2

-- | For keys that appear in both maps, the given function decides whether the
-- key is removed from the first map.
--
-- You can use 'andLeft' and 'andRight' to obtain @'Key' s k@ and @'Key' t k@
-- respectively.
differenceWithKey
  :: forall s t k a b. Hashable k
  => (Refined (InSet 'Hashed s && InSet 'Hashed t) k -> a -> b -> Maybe a)
  -> HashMap s k a
  -> HashMap t k b
  -> SomeHashMapWith (PartialDifferenceProof 'Hashed s t) k a
differenceWithKey f (HashMap m1) (HashMap m2) = SomeHashMapWith
  (HashMap $ HashMap.differenceWith
    (\x (k, y) -> f (reallyUnsafeRefine k) x y)
    m1
    (HashMap.mapWithKey (,) m2))
  $ PartialDifferenceProof unsafeSubset unsafeSubset

-- | Return the intersection of two maps with the given combining function.
--
-- You can use 'andLeft' and 'andRight' to obtain @'Key' s k@ and @'Key' t k@
-- respectively.
intersectionWithKey
  :: forall s t k a b c. Hashable k
  => (Refined (InSet 'Hashed s && InSet 'Hashed t) k -> a -> b -> c)
  -> HashMap s k a
  -> HashMap t k b
  -> SomeHashMapWith (IntersectionProof 'Hashed s t) k c
intersectionWithKey f (HashMap m1) (HashMap m2) = SomeHashMapWith
  (HashMap $ HashMap.intersectionWithKey (f . reallyUnsafeRefine) m1 m2)
  $ IntersectionProof unsafeSubset unsafeSubsetWith2

-- | Apply a function to all values in a map, together with their corresponding
-- keys, that are proven to be in the map. The set of keys remains the same.
mapWithKey
  :: forall s k a b. (Key s k -> a -> b) -> HashMap s k a -> HashMap s k b
mapWithKey = gcoerceWith (unsafeCastKey @s @k) $ coerce
  $ HashMap.mapWithKey @k @a @b

-- | Map an 'Applicative' transformation with access to each value's
-- corresponding key and a proof that it is in the map. The set of keys remains
-- unchanged.
traverseWithKey
  :: forall s f k a b. Applicative f
  => (Key s k -> a -> f b) -> HashMap s k a -> f (HashMap s k b)
traverseWithKey f (HashMap m)
  = HashMap <$> HashMap.traverseWithKey (f . unsafeKey) m

-- | Thread an accumularing argument through the map in ascending order of
-- hashes.
mapAccumLWithKey
  :: forall s k a b c. (a -> Key s k -> b -> (a, c))
  -> a
  -> HashMap s k b
  -> (a, HashMap s k c)
mapAccumLWithKey f = imapAccumL (flip f)

-- | Thread an accumularing argument through the map in descending order of
-- hashes.
mapAccumRWithKey
  :: forall s k a b c. (a -> Key s k -> b -> (a, c))
  -> a
  -> HashMap s k b
  -> (a, HashMap s k c)
mapAccumRWithKey f = imapAccumR (flip f)

-- | @'mapKeysWith' c f m@ applies @f@ to each key of @m@ and collects the
-- results into a new map. For keys that were mapped to the same new key, @c@
-- acts as the combining function for corresponding values.
mapKeysWith
  :: forall s k1 k2 a. Hashable k2
  => (a -> a -> a)
  -> (Key s k1 -> k2)
  -> HashMap s k1 a
  -> SomeHashMapWith (MapProof 'Hashed s k1 k2) k2 a
mapKeysWith f g (HashMap m) = SomeHashMapWith
  (HashMap $ HashMap.fromListWith f
    $ HashMap.foldrWithKey (\k x xs -> (g $ unsafeKey k, x) : xs) [] m)
  $ MapProof (unsafeKey . g) \k2 ->
    case HashMap.lookup (unrefine k2) backMap of
      Nothing -> error
        "mapKeysWith: bug: Data.HashMap.Refined has been subverted"
      Just k1 -> k1
  where
    ~backMap = HashMap.fromList
      [ (k2, unsafeKey k1)
      | k1 <- HashMap.keys m
      , let !k2 = g $ unsafeKey k1
      ]

-- | Apply a function to all values in a map, together with their corresponding
-- keys, and collect only the 'Just' results, returning a potentially smaller
-- map.
mapMaybeWithKey
  :: forall s k a b. (Key s k -> a -> Maybe b)
  -> HashMap s k a
  -> SomeHashMapWith (SupersetProof 'Hashed s) k b
mapMaybeWithKey f (HashMap m)
  = SomeHashMapWith (HashMap $ HashMap.mapMaybeWithKey (f . unsafeKey) m)
    $ SupersetProof unsafeSubset

-- | Apply a function to all values in a map, together with their corresponding
-- keys, and collect the 'Left' and 'Right' results into separate (disjoint)
-- maps.
mapEitherWithKey
  :: forall s k a b c. Hashable k -- TODO: this is only used in the proof
  => (Key s k -> a -> Either b c)
  -> HashMap s k a
  -> Some2HashMapWith (PartitionProof 'Hashed s k) k b c
mapEitherWithKey p (HashMap m)
  | m' <- HashMap.mapWithKey (p . unsafeKey) m
  = Some2HashMapWith
    (HashMap $ HashMap.mapMaybe (either Just (const Nothing)) m')
    (HashMap $ HashMap.mapMaybe (either (const Nothing) Just) m')
    $ PartitionProof
      do \k -> case HashMap.lookup (unrefine k) m of
          Nothing -> error
            "mapEitherWithKey: bug: Data.HashMap.Refined has been subverted"
          Just x -> case p k x of
            Left _ -> Left $ unsafeKey $ unrefine k
            Right _ -> Right $ unsafeKey $ unrefine k
      unsafeSubset unsafeSubsetWith2 \f g -> unsafeSubsetWith2 f g

-- | @'bind' m f@ is a map that for each key @k :: 'Key' s k@, contains the
-- value @f (m '!' k) '!' k@, similar to @'>>='@ for functions.
bind
  :: forall s k a b. Hashable k
  => HashMap s k a -> (a -> HashMap s k b) -> HashMap s k b
bind m f = mapWithKey (\k x -> f x ! k) m

-- | Apply the inverse image of the given function to the keys of the given map,
-- so that for all @k :: 'Key' s2 k2@,
-- @'backpermuteKeys' f m '!' k = m '!' f k@.
--
-- If maps are identified with functions, this computes the composition.
backpermuteKeys
  :: forall s1 s2 k1 k2 a. (Hashable k1, KnownHashSet s2 k2)
  => (Key s2 k2 -> Key s1 k1) -> HashMap s1 k1 a -> HashMap s2 k2 a
backpermuteKeys f m = fromSet \k -> m ! f k
