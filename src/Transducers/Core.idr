module Transducers.Core

import Control.Monad.State


--------------------------------------------------------------------------------
-- Core (definition of a step)
--------------------------------------------------------------------------------

public export
data Status a = Done a | Continue a

export
unStatus : Status a -> a
unStatus (Done a) = a
unStatus (Continue a) = a

export
implementation Functor Status where
  map f (Done a) = Done (f a)
  map f (Continue a) = Continue (f a)

public export
StatelessStep : (acc, elem: Type) -> Type
StatelessStep acc elem = acc -> elem -> acc

public export
Step : (state, acc, elem: Type) -> Type
Step state acc elem = acc -> elem -> State state (Status acc)

public export
record Reducer st acc elem where
  constructor MkReducer
  state : st
  runStep : Step st acc elem
  complete : st -> acc -> acc

noStateStep : StatelessStep acc elem -> Reducer () acc elem
noStateStep fn = MkReducer () step (const id)
  where step acc x = pure $ Continue (fn acc x)

public export
Transducer : (acc, s1, s2, inner, outer: Type) -> Type
Transducer acc s1 s2 inner outer = Reducer s1 acc inner -> Reducer s2 acc outer


--------------------------------------------------------------------------------
-- Helpers to build stateless Reducers and Transducers
--------------------------------------------------------------------------------

export
statelessTransducer : (Step s acc inner -> Step s acc outer) -> Transducer acc s s inner outer
statelessTransducer onStep xf = MkReducer (state xf) (onStep (runStep xf)) (complete xf)

export
makeTransducer :
    s'
    -> (Step s acc inner -> Step s (s', acc) outer)
    -> (Step s acc inner -> s' -> acc -> State s acc)
    -> Transducer acc s (s', s) inner outer
makeTransducer initState onStep onComplete xf =
  MkReducer (initState, state xf) stepImpl completeImpl
  where
    completeImpl (s', s) acc =
      complete xf s $ evalState (onComplete (runStep xf) s' acc) s
    stepImpl acc elem = do
      (s1', s1) <- get
      let (result, s2) = runState (onStep (runStep xf) (s1', acc) elem) s1
      case result of
        (Done (s2', acc)) => do put (s2', s2); pure (Done acc)
        (Continue (s2', acc)) => do put (s2', s2); pure (Continue acc)

export
statefulTransducer : s' -> (Step s acc inner -> Step s (s', acc) outer) -> Transducer acc s (s', s) inner outer
statefulTransducer initState onStep = makeTransducer initState onStep onComplete
  where
    onComplete next _ acc = pure acc

export
withState : s -> Status acc -> Status (s, acc)
withState s = map (\acc => (s, acc))


--------------------------------------------------------------------------------
-- Core (Reductions)
--------------------------------------------------------------------------------

export
runSteps : (Foldable t) => Step st acc elem -> acc -> t elem -> State st (Status acc)
runSteps step acc elems = foldr stepImpl (pure . id) elems (Continue acc)
  where
    stepImpl _ nextIteration (Done acc) = pure (Done acc)
    stepImpl elem nextIteration (Continue acc) = step acc elem >>= nextIteration

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
