> module Data.Nat where

Esto se puede mover a otro módulo (o usar alguna implementación
 externa)

> data Nat = Z | S Nat deriving (Eq, Ord, Read, Show)
