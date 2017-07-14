# Idris Reducers

Implementation a reducer-like library in Idris, inspired by the great Clojure reducer library: https://clojure.org/reference/reducers.

The goal is to provide reductions step (the accumulating function of foldl) that:

* Can be composed without the overhead of creating intermediary lists
* Remains simple to write, read and reason about

Here are some examples of transformations we can write:

    -- Standard Idris (creating intermediary lists)
    foldl (+) 0 (map (+1) (concatMap twice (filter odd [1..100])))

    -- Using the reducer library
    foldl (filtering odd |> catMapping twice |> mapping (+1) (+)) 0 [1..100]
