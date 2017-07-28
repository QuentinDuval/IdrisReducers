module Transducers.Algorithms


import Control.Monad.State
import Transducers.Core

--------------------------------------------------------------------------------
-- Basic Transducers (stateless)
--------------------------------------------------------------------------------

export
mapping : (a -> b) -> Transducer acc s s a b
mapping fn = statelessTransducer $ \next, acc, outer => next acc (fn outer)

export
filtering : (a -> Bool) -> Transducer acc s s a a
filtering pf = statelessTransducer $
  \next, acc, a =>
    if pf a
      then next acc a
      else pure (Continue acc)

export
catMapping : (Foldable t) => (a -> t b) -> Transducer acc s s a b
catMapping fn = statelessTransducer $
  \next, acc, a => runSteps next acc (fn a)

export
takingWhile : (a -> Bool) -> Transducer acc s s a a
takingWhile p = statelessTransducer $
  \next, acc, a => do
    if p a
      then next acc a
      else pure (Done acc)


--------------------------------------------------------------------------------
-- Basic Transducers (stateful)
--------------------------------------------------------------------------------

export
dropping : Nat -> Transducer acc s (Nat, s) a a
dropping n = statefulTransducer n dropImpl
  where
    dropImpl next (S n, acc) _ = pure $ Continue (n, acc)
    dropImpl next (Z, acc) a = withState Z <$> next acc a

export
taking : Nat -> Transducer acc s (Nat, s) a a
taking n = statefulTransducer n takeImpl
  where
    takeImpl next (Z, acc) a = pure (Done (Z, acc))
    takeImpl next (n, acc) a = withState (pred n) <$> next acc a

export
interspersing : a -> Transducer acc s (Bool, s) a a
interspersing separator = statefulTransducer False stepImpl
  where
    stepImpl next (False, acc) a = withState True <$> next acc a
    stepImpl next (True, acc) a =
      withState True <$> runSteps next acc [separator, a]

export
indexingFrom : Int -> Transducer acc s (Int, s) a (Int, a)
indexingFrom startIndex = statefulTransducer startIndex stepImpl
  where
    stepImpl next (n, acc) a = withState (succ n) <$> next acc (n, a)

export
indexing : Transducer acc s (Int, s) a (Int, a)
indexing = indexingFrom 0

export
chunksOf : Nat -> Transducer acc s (List a, s) a (List a)
chunksOf chunkSize = makeTransducer [] nextChunk dumpRemaining
  where
    nextChunk next (remaining, acc) a =
      let remaining' = a :: remaining in
      if length remaining' == chunkSize
        then withState [] <$> next acc (reverse remaining')
        else pure $ Continue (remaining', acc)
    dumpRemaining next remaining acc =
      if isNil remaining
        then pure acc
        else unStatus <$> next acc (reverse remaining)

export
deduplicate : (Eq a) => Transducer acc s (Maybe a, s) a a
deduplicate = statefulTransducer Nothing stepImpl
  where
    stepImpl next (oldVal, acc) a =
      if oldVal == Just a
        then pure $ Continue (oldVal, acc)
        else withState (Just a) <$> next acc a

export
groupingBy : (a -> a -> Bool) -> Transducer acc s (List a, s) a (List a)
groupingBy sameGroup = makeTransducer [] stepImpl dumpRemaining
  where
    stepImpl next (previousVals, acc) a =
      case nonEmpty previousVals of
        No _ => pure $ Continue ([a], acc)
        Yes _ => if sameGroup a (head previousVals)
          then pure $ Continue (a :: previousVals, acc)
          else withState [a] <$> next acc (reverse previousVals)
    dumpRemaining next remaining acc =
      if isNil remaining
        then pure acc
        else unStatus <$> next acc (reverse remaining)


--------------------------------------------------------------------------------
-- Higher order transducers
--------------------------------------------------------------------------------

public export
record Iso a b where
  constructor MkIso
  toIso : a -> b
  fromIso : b -> a

export
under : Iso a b -> Transducer acc s1 s2 b b -> Transducer acc s1 s2 a a
under iso xf = mapping (toIso iso) . xf . mapping (fromIso iso)
