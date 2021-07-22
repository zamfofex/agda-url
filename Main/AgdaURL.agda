{-# OPTIONS --guardedness #-}

module Main.AgdaURL where

open import Data.URL as URL using (URL ; generic-mode)
open import IO using (IO ; _>>=_ ; _>>_ ; return ; getLine ; putStrLn ; putStr ; run)
open import Function using (case_of_)
open import Data.Maybe using (just ; nothing)
open import Data.List using (List ; [] ; _∷_)
open import Data.String using (String ; _++_)

main = run do
   line ← getLine
   let url = URL.parse line
   let strs = case url of λ { (just url) → info url ; nothing → "[ invalid URL ]" ∷ [] }
   IO.List.mapM putStrLn strs
   where
   info : URL → List String
   info url =
     ("serialized: " ++ URL.print url) ∷
     ("scheme: " ++ URL.print-scheme′ (URL.scheme url)) ∷
     ("authority: " ++ URL.print-authority′ (URL.authority url)) ∷
     ("drive: " ++ URL.print-drive′ (URL.drive url)) ∷
     ("path: " ++ URL.print-path (URL.path url)) ∷
     ("query: " ++ URL.print-query′ (URL.query url)) ∷
     ("fragment: " ++ URL.print-fragment′ (URL.fragment url)) ∷ []
