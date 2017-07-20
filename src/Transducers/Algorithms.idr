module Transducers.Algorithms


import Control.Monad.State
import Transducers.Core

--------------------------------------------------------------------------------
-- Basic Transducers (stateless)
--------------------------------------------------------------------------------

export
mapping : (outer -> inner) -> Transducer s s inner outer
mapping fn = statelessTransducer $ \next, acc, outer => next acc (fn outer)

export
filtering : (elem -> Bool) -> Transducer s s elem elem
filtering pf = statelessTransducer $
  \next, acc, elem =>
    if pf elem
      then next acc elem
      else pure (Continue acc)

export
catMapping : (Foldable t) => (outer -> t inner) -> Transducer s s inner outer
catMapping fn = statelessTransducer $
  \next, acc, outer => runSteps next acc (fn outer)

{-
export
takingWhile : (acc -> Bool) -> Transducer s s elem elem
takingWhile p = statelessTransducer $
  \next, acc, elem => do
    acc' <- next acc elem
    if p (unStatus acc')
      then pure acc'
      else pure (Done $ unStatus acc')
-}

--------------------------------------------------------------------------------
-- Basic Transducers (stateful)
--------------------------------------------------------------------------------

export
dropping : Nat -> Transducer s (Nat, s) elem elem
dropping n = statefulTransducer n dropImpl
  where
    dropImpl : Step s acc elem -> (Nat, acc) -> elem -> State s (Status (Nat, acc))
    dropImpl next (S n, acc) e = pure $ Continue (n, acc)
    dropImpl next (Z, acc) e = withState Z <$> next acc e


export
taking : Nat -> Transducer s (Nat, s) elem elem
taking n = statefulTransducer n takeImpl
  where
    takeImpl : Step s acc elem -> (Nat, acc) -> elem -> State s (Status (Nat, acc))
    takeImpl next (Z, acc) e = pure (Done (Z, acc))
    takeImpl next (n, acc) e = withState (pred n) <$> next acc e

export
interspersing : elem -> Transducer s (Bool, s) elem elem
interspersing separator = statefulTransducer False stepImpl
  where
    stepImpl : Step s acc elem -> (Bool, acc) -> elem -> State s (Status (Bool, acc))
    stepImpl next (False, acc) e = withState True <$> next acc e
    stepImpl next (True, acc) e =
      withState True <$> runSteps next acc [separator, e]

export
indexingFrom : Int -> Transducer s (Int, s) (Int, elem) elem
indexingFrom startIndex = statefulTransducer startIndex stepImpl
  where
    stepImpl : Step s acc (Int, elem) -> (Int, acc) -> elem -> State s (Status (Int, acc))
    stepImpl next (n, acc) e = withState (succ n) <$> next acc (n, e)

export
indexing : Transducer s (Int, s) (Int, elem) elem
indexing = indexingFrom 0

export
chunksOf : Nat -> Transducer s (List elem, s) (List elem) elem
chunksOf chunkSize = makeTransducer [] nextChunk dumpRemaining
  where

    nextChunk : Step s acc (List elem) -> (List elem, acc) -> elem -> State s (Status (List elem, acc))
    nextChunk next (remaining, acc) e =
      let remaining' = e :: remaining in
      if length remaining' == chunkSize
        then withState [] <$> next acc (reverse remaining')
        else pure $ Continue (remaining', acc)

    dumpRemaining : Step s acc (List elem) -> List elem -> acc -> State s acc
    dumpRemaining next remaining acc =
      if length remaining == 0
        then pure acc
        else unStatus <$> next acc (reverse remaining)

export
deduplicate : (Eq elem) => Transducer s (Maybe elem, s) elem elem
deduplicate = statefulTransducer Nothing stepImpl
  where
    stepImpl : (Eq elem) => Step s acc elem -> (Maybe elem, acc) -> elem -> State s (Status (Maybe elem, acc))
    stepImpl next (oldVal, acc) e =
      if oldVal == Just e
        then pure $ Continue (oldVal, acc)
        else withState (Just e) <$> next acc e
