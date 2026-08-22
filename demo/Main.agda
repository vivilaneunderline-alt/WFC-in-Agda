{-# OPTIONS --guardedness #-}

module Main where

open import IO
open import Parser using (runInput)

main : Main
main = run do
  putStrLn "Input format: gridSize:threshold:patterns:seed:"
  input ← getLine
  putStrLn (runInput input)
