{-# OPTIONS --guardedness #-}

module Main.AgdaURL where

open import Data.URL as URL using (URL ; forced-resolve)
open import IO using (IO ; _>>=_ ; _>>_ ; return ; getLine ; putStrLn ; run)
open import Function using (case_of_ ; _$_ ; id)
open import Data.Maybe as Maybe using (just ; nothing ; maybe)
open import Data.List using (List ; _∷_ ; [] ; [_])
open import Data.String using (String ; _++_)
open import Data.Product using (_,_)

main = run do
   putStrLn "Target URL:"
   line ← getLine
   putLn
   
   let url₁ = URL.parse line
   putStrLns $ maybe info [ "[ invalid URL 1 ]" ] url₁
   putLn
   
   putStrLn "Base URL:"
   line ← getLine
   putLn
   
   let url₂ = URL.parse line
   putStrLns $ maybe info [ "[ invalid URL 2 ]" ] url₂
   putLn
   
   putStrLn "Resolved URL:"
   putLn
   
   let url₃ = Maybe.ap (Maybe.map forced-resolve url₁) url₂ Maybe.>>= id
   putStrLns $ maybe info [ "[ could not resolve ]" ] url₃

   where
   putStrLns = IO.List.mapM putStrLn
   putLn = putStrLn ""
   
   info : URL → List String
   info url =
     ("href:   " ++ URL.print url) ∷
     ("scheme: " ++ URL.print-scheme′ (URL.scheme url)) ∷
     ("auth:   " ++ URL.print-authority′ (URL.authority url)) ∷
     ("drive:  " ++ URL.print-drive′ (URL.drive url)) ∷
     ("path:   " ++ URL.print-path (URL.path url)) ∷
     ("query:  " ++ URL.print-query′ (URL.query url)) ∷
     ("frag:   " ++ URL.print-fragment′ (URL.fragment url)) ∷ []
