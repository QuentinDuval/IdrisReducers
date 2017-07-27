module Transducers.Utils


--------------------------------------------------------------------------------
-- Utils to conjoin elements to a container
--------------------------------------------------------------------------------

public export
interface Conj xs x where
  conj : xs -> x -> xs

export
implementation Conj (List a) a where
  conj xs x = x :: xs

export
implementation Conj String Char where
  conj xs x = xs ++ singleton x


--------------------------------------------------------------------------------
-- Utils to conjoin the result of a transduce into a container
--------------------------------------------------------------------------------

-- TODO
