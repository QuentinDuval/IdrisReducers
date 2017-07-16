module Transducers.Core2

import Control.Monad.State


--------------------------------------------------------------------------------
-- Core (definition of a step)
--------------------------------------------------------------------------------

export
data Status a = Done a | Continue a

export
unStatus : Status a -> a
unStatus (Done a) = a
unStatus (Continue a) = a

export
implementation Functor Status where
  map f (Done a) = Done (f a)
  map f (Continue a) = Continue (f a)

export
StatelessStep : (acc, elem: Type) -> Type
StatelessStep acc elem = acc -> elem -> acc

export
Step : (state, acc, elem: Type) -> Type
Step state acc elem = acc -> elem -> State state (Status acc)

public export
record Reducer st acc elem where
  constructor MkReducer
  state : st
  runStep : Step st acc elem
  complete : st -> acc -> acc

public export
Transducer : (acc, s1, s2, inner, outer: Type) -> Type
Transducer acc s1 s2 inner outer = Reducer s1 acc inner -> Reducer s2 acc outer


--------------------------------------------------------------------------------
-- Helpers to build stateless Reducers and Transducers
--------------------------------------------------------------------------------

noStateStep : StatelessStep acc elem -> Reducer () acc elem
noStateStep fn = MkReducer () step (const id)
  where step acc x = pure $ Continue (fn acc x)

export
statelessTransducer : (Step s acc inner -> Step s acc outer) -> Transducer acc s s inner outer
statelessTransducer onStep xf = MkReducer (state xf) (onStep (runStep xf)) (complete xf)

export
statefulTransducer : s' -> (Step s acc inner -> Step s (s', acc) outer) -> Transducer acc s (s', s) inner outer
statefulTransducer initState onStep xf = MkReducer
  (initState, state xf)
  stepImpl
  (\state => complete xf (snd state))
  where
    stepImpl acc elem = do
      (s1', s1) <- get
      let (result, s2) = runState (onStep (runStep xf) (s1', acc) elem) s1
      case result of
        (Done (s2', acc)) => do put (s2', s2); pure (Done acc)
        (Continue (s2', acc)) => do put (s2', s2); pure (Continue acc)

export
withState : s -> Status acc -> Status (s, acc)
withState s = map (\acc => (s, acc))


--------------------------------------------------------------------------------
-- Core (Reductions)
--------------------------------------------------------------------------------

foldlM : (Foldable t, Monad m) => (funcM: a -> Lazy b -> m a) -> (init: a) -> (input: t b) -> m a
foldlM fm a0 = foldl (\ma,b => ma >>= flip fm b) (pure a0)

export
runSteps : (Foldable t) => Step st acc elem -> acc -> t elem -> State st (Status acc)
runSteps step acc elems = foldlM stepImpl (Continue acc) elems
  where
    stepImpl (Done acc) _ = pure (Done acc)
    stepImpl (Continue acc) elem = step acc (Force elem)

export
reduce : (Foldable t) => Reducer st acc elem -> acc -> t elem -> acc
reduce step acc =
  uncurry (complete step)
    . (\(acc, s) => (s, unStatus acc))
    . (flip runState (state step))
    . runSteps (runStep step) acc

export
transduce : (Foldable t) => Transducer acc () s a b -> (acc -> a -> acc) -> acc -> t b -> acc
transduce xf step = reduce (xf (noStateStep step))

-- TODO: keep it without monad inside?
-- unwrapState : Step st acc elem -> (st -> acc -> elem -> (s, Status elem))


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


--------------------------------------------------------------------------------
-- Basic Transducers (stateful)
--------------------------------------------------------------------------------

export
taking : Nat -> Transducer acc s (Nat, s) elem elem
taking n = statefulTransducer n takeImpl
  where
    takeImpl next (Z, acc) elem = pure (Done (Z, acc))
    takeImpl next (n, acc) elem = do
      acc' <- next acc elem
      pure $ withState (pred n) acc'


--------------------------------------------------------------------------------
-- Tests
--------------------------------------------------------------------------------

run_tests : IO ()
run_tests = do
  print $ foldl (+) 0 (map (+1) [0..9])
  print $ transduce (mapping (+1)) (+) 0 [0..9]
  pure ()
