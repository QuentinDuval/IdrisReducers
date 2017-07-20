module Transducers.Algorithms


import Control.Monad.State
import Transducers.Core

--------------------------------------------------------------------------------
-- Basic Transducers (stateless)
--------------------------------------------------------------------------------

export
mapping : (outer -> inner) -> Transducer acc s s inner outer
mapping fn = statelessTransducer $ \next, acc, outer => next acc (fn outer)

export
filtering : (elem -> Bool) -> Transducer acc s s elem elem
filtering pf = statelessTransducer $
  \next, acc, elem =>
    if pf elem
      then next acc elem
      else pure (Continue acc)

export
catMapping : (Foldable t) => (outer -> t inner) -> Transducer acc s s inner outer
catMapping fn = statelessTransducer $
  \next, acc, outer => runSteps next acc (fn outer)

export
takingWhile : (elem -> Bool) -> Transducer acc s s elem elem
takingWhile p = statelessTransducer $
  \next, acc, elem => do
    acc' <- next acc elem
    if p elem
      then pure acc'
      else pure (Done $ unStatus acc')


--------------------------------------------------------------------------------
-- Basic Transducers (stateful)
--------------------------------------------------------------------------------

export
dropping : Nat -> Transducer acc s (Nat, s) elem elem
dropping n = statefulTransducer n dropImpl
  where
    dropImpl next (S n, acc) e = pure $ Continue (n, acc)
    dropImpl next (Z, acc) e = withState Z <$> next acc e

export
taking : Nat -> Transducer acc s (Nat, s) elem elem
taking n = statefulTransducer n takeImpl
  where
    takeImpl next (Z, acc) e = pure (Done (Z, acc))
    takeImpl next (n, acc) e = withState (pred n) <$> next acc e

export
interspersing : elem -> Transducer acc s (Bool, s) elem elem
interspersing separator = statefulTransducer False stepImpl
  where
    stepImpl next (False, acc) e = withState True <$> next acc e
    stepImpl next (True, acc) e =
      withState True <$> runSteps next acc [separator, e]

export
indexingFrom : Int -> Transducer acc s (Int, s) (Int, elem) elem
indexingFrom startIndex = statefulTransducer startIndex stepImpl
  where
    stepImpl next (n, acc) e = withState (succ n) <$> next acc (n, e)

export
indexing : Transducer acc s (Int, s) (Int, elem) elem
indexing = indexingFrom 0

export
chunksOf : Nat -> Transducer acc s (List elem, s) (List elem) elem
chunksOf chunkSize = makeTransducer [] nextChunk dumpRemaining
  where
    nextChunk next (remaining, acc) e =
      let remaining' = e :: remaining in
      if length remaining' == chunkSize
        then withState [] <$> next acc (reverse remaining')
        else pure $ Continue (remaining', acc)
    dumpRemaining next remaining acc =
      if length remaining == 0
        then pure acc
        else unStatus <$> next acc (reverse remaining)

export
deduplicate : (Eq elem) => Transducer acc s (Maybe elem, s) elem elem
deduplicate = statefulTransducer Nothing stepImpl
  where
    stepImpl next (oldVal, acc) e =
      if oldVal == Just e
        then pure $ Continue (oldVal, acc)
        else withState (Just e) <$> next acc e
