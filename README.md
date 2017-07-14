# Idris Reducers

Implementation a reducer-like library in Idris, inspired by the great Clojure reducer library: https://clojure.org/reference/reducers.

## Goal & Motivation

The goal is to provide reductions step (the accumulating function of foldl) that:

* Can be composed without the overhead of creating intermediary lists
* Remains simple to write, read and reason about

## Example

Here are some examples of transformations we can write:

    -- Standard Idris (creating intermediary lists)
    foldl (+) 0 (map (+1) (concatMap twice (filter odd [1..100])))

    -- Using the reducer library
    foldl (filtering odd |> catMapping twice |> mapping (+1) (+)) 0 [1..100]

The above code takes as input a list of integers between 1 and 100, and:

* Filter the odd numbers out of it
* Repeat of each of these number twice
* Add one to each numbers
* Sum them all
