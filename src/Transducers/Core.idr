module Transducers.Core


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
Step state acc elem = state -> acc -> elem -> Status (state, acc)

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

export
noStateStep : StatelessStep acc elem -> Reducer () acc elem
noStateStep fn = MkReducer () step (const id)
  where step = \_, acc, elem => Continue ((), fn acc elem)

export
updateState : s' -> Status (s, acc) -> Status ((s', s), acc)
updateState s' = map (\(s, acc) => ((s', s), acc))

export
statelessTransducer : (Step s acc inner -> Step s acc outer) -> Transducer acc s s inner outer
statelessTransducer onStep xf = MkReducer (state xf) (onStep (runStep xf)) (complete xf)

export
statefulTransducer : s' -> (Step s acc inner -> Step (s', s) acc outer) -> Transducer acc s (s', s) inner outer
statefulTransducer initState onStep xf = MkReducer
  (initState, state xf)
  (onStep (runStep xf))
  (\state => complete xf (snd state))

-- TODO: to make the transfer of state better:
-- * Use a State Monad to thread the wrapped state?
-- * Could be used to specific the runStep, and maybe even complete and init

-- TransducePipe : (state, val: Type) -> Type
-- TransducePipe state val = State state val


--------------------------------------------------------------------------------
-- Core (Reductions)
--------------------------------------------------------------------------------

export
runSteps : (Foldable t) => Step st acc elem -> (st, acc) -> t elem -> Status (st, acc)
runSteps step start elems =
  foldr compStep id elems (Continue start) -- TODO: is it really not consuming all elements anyway?
  where
    compStep elem nextIteration result =
      case result of
        Done done => Done done
        Continue (st, acc) => nextIteration (step st acc elem)

export
reduce : (Foldable t) => Reducer st acc elem -> acc -> t elem -> acc
reduce step result =
  uncurry (complete step)
    . unStatus
    . runSteps (runStep step) (state step, result)

export
transduce : (Foldable t) => Transducer acc () s a b -> (acc -> a -> acc) -> acc -> t b -> acc
transduce xf step = reduce (xf (noStateStep step))


--------------------------------------------------------------------------------
-- Core (syntaxic sugar to compose Transducers)
--------------------------------------------------------------------------------

infixr 5 |>

export
(|>) : (b -> c) -> (a -> b) -> (a -> c)
(|>) r2 r1 = r2 . r1


--------------------------------------------------------------------------------
-- Basic Transducers (stateless)
--------------------------------------------------------------------------------

export
mapping : (outer -> inner) -> Transducer acc s s inner outer
mapping fn = statelessTransducer $
  \next, st, acc, outer => next st acc (fn outer)

export
filtering : (elem -> Bool) -> Transducer acc s s elem elem
filtering pf = statelessTransducer $
  \next, st, acc, elem =>
    if pf elem then next st acc elem else Continue (st, acc)

export
catMapping : (Foldable t) => (outer -> t inner) -> Transducer acc s s inner outer
catMapping fn = statelessTransducer $
  \next, st, acc, outer => runSteps next (st, acc) (fn outer)


--------------------------------------------------------------------------------
-- Basic Transducers (stateful)
--------------------------------------------------------------------------------

export
dropping : Nat -> Transducer acc s (Nat, s) elem elem
dropping n = statefulTransducer n dropImpl
  where
    dropImpl next (S n, st) acc elem = Continue ((n, st), acc)
    dropImpl next (Z, st) acc elem =
      updateState Z (next st acc elem)

export
taking : Nat -> Transducer acc s (Nat, s) elem elem
taking n = statefulTransducer n takeImpl
  where
    takeImpl next (Z, st) acc elem = Done ((Z, st), acc)
    takeImpl next (n, st) acc elem =
      updateState (pred n) (next st acc elem)

export
interspersing : elem -> Transducer acc s (Bool, s) elem elem
interspersing separator = statefulTransducer False stepImpl
  where
    stepImpl next (False, st) acc e =
      updateState True (next st acc e)
    stepImpl next (True, st) acc e =
      updateState True (runSteps next (st, acc) [separator, e])

export
indexingFrom : Int -> Transducer acc s (Int, s) (Int, elem) elem
indexingFrom startIndex = statefulTransducer startIndex stepImpl
  where
    stepImpl next (n, st) acc e =
      updateState (succ n) (next st acc (n, e))

export
indexing : Transducer acc s (Int, s) (Int, elem) elem
indexing = indexingFrom 0

export
chunksOf : Nat -> Transducer acc s (List elem, s) (List elem) elem
chunksOf chunkSize xf = MkReducer ([], state xf) nextChunk dumpRemaining
  where
    nextChunk (remaining, st) acc elem =
      let remaining' = elem :: remaining in
      if length remaining' == chunkSize
        then updateState [] $ runStep xf st acc (reverse remaining')
        else updateState remaining' $ Continue (st, acc)
    dumpRemaining (remaining, st) acc =
      let (st', acc') =
            if length remaining == 0
              then (st, acc)
              else unStatus (runStep xf st acc (reverse remaining))
      in complete xf st' acc'

-- TODO: unique and deduplicate
