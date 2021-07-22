module Data.URL where

open import Data.String using (String ; toList ; fromList ; _++_)
open import Data.Nat using (ℕ ; _^_ ; _≟_ ; _<?_ ; _+_ ; _∸_ ; _*_)
open import Data.Fin using (Fin ; fromℕ<)
open import Data.Empty using (⊥)
open import Data.Bool using (Bool ; true ; false ; if_then_else_)
open import Data.Char using (Char ; toℕ ; fromℕ ; _≤?_) renaming (_≟_ to _≟ᶜ_)
open import Data.Char.Properties using (≤-decPoset)
open import Text.Regex ≤-decPoset
   using (Exp ; Match ; [_] ; [^_] ; _─_ ; _∣_ ; _∙_ ; _∈_ ; _⋆ ; _+ ; · ; singleton ; ε ; ∅)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.List
   using (List ; _∷_ ; [] ; drop ; map ; length ; concatMap ; dropWhile ; reverse ; filter ; foldr)
   renaming (linesBy to split ; _++_ to _++ᴸ_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise)
open import Text.Regex.Search ≤-decPoset using (module Whole ; module Prefix)
open import Relation.Binary using (Decidable)
open import Data.Maybe as Maybe using (Maybe ; maybe ; maybe′ ; fromMaybe ; just ; nothing ; is-just)
open import Function using (_∘_ ; _$_ ; flip ; id ; const)
open import Data.Unit using (⊤ ; tt)
open import Category.Monad.State using (StateT ; StateTMonad)
open import Data.Product as Σ using (_,_ ; map₁ ; proj₁ ; _×_)
open import Category.Monad using (RawMonad)
open import Data.Maybe.Categorical as Maybe using ()
open RawMonad (StateTMonad String Maybe.monad) using (_>>=_ ; _>>_ ; return)
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Nullary.Product using () renaming (_×-dec_ to _and_)
open import Relation.Nullary.Negation using (¬?)

-- Preliminaries
private
   decimal hex-upper hex-lower hex : Exp
   alpha-upper alpha-lower alpha : Exp
   nonempty : Exp
   
   decimal = [ '0' ─ '9' ∷ [] ]
   hex-upper = [ 'A' ─ 'F' ∷ [] ]
   hex-lower = [ 'a' ─ 'f' ∷ [] ]
   alpha-upper = [ 'A' ─ 'Z' ∷ [] ]
   alpha-lower = [ 'a' ─ 'z' ∷ [] ]
   hex = decimal ∣ hex-upper ∣ hex-lower
   alpha = alpha-upper ∣ alpha-lower
   nonempty = · +
   
   _::_ : String → Exp → Set
   _::_ = Match (Pointwise _≡_) ∘ toList
   
   _is?_ : Decidable _::_
   _is?_ = Whole.search ∘ toList
   
   -- Simple monad for parsing strings.
   
   Parser : Set → Set
   Parser = StateT String Maybe
   
   try : ∀ {A} → Parser A → Parser (Maybe A)
   try f str = maybe (just ∘ map₁ just) (just $ nothing , str) (f str)
   
   assert : ∀ {A} → Dec A → Parser A
   assert (yes p) = return p
   assert (no _) = const nothing
   
   end : Parser ⊤
   end str with length (toList str) ≟ 0
   ... | yes _ = just $ tt , ""
   ... | no _ = nothing
   
   -- Parsing operations based on regexes.
   
   -- TODO: Preserve the match proof somehow.
   -- TODO: Maybe by adding a variant that drops it,
   -- TODO: in order to avoid sacrificing convenience of usage for simple cases.
   longest : Exp → Parser String
   longest exp str with Prefix.longest (toList str) exp
   ... | yes match = just $ fromList list-match , (fromList $ drop (length list-match) (toList str))
      where list-match = Match.list match
   ... | no _ = nothing
   
   single : Char → Parser ⊤
   single ch = do
      longest $ singleton ch
      return tt

-- TODO
IPv4 = ⊥
IPv6 = ⊥
Domain = ⊥

Port : Set
Port = Fin (2 ^ 16)

scheme-regex : Exp
drive-regex : Exp
file-regex : Exp

ValidScheme : String → Set
ValidDrive : String → Set
ValidFile : String → Set

scheme-regex = alpha ∙ (alpha ∣ decimal ∣ [ map [_] $ toList "+-." ]) ⋆
drive-regex = alpha ∙ [ map [_] $ toList ":|" ]
file-regex = nonempty

ValidScheme scheme = scheme :: scheme-regex
ValidDrive drive = drive :: drive-regex
ValidFile file = file :: drive-regex

data Host : Set where
   domain-host : Domain → Host
   ipv4-host : IPv4 → Host
   ipv6-host : IPv6 → Host
   opaque-host : String → Host

record Authority : Set where
   constructor mkAuthority
   field username : Maybe String
   field password : Maybe String
   field host : Maybe Host
   field port : Maybe Port

record Path : Set where
   constructor mkPath
   field path-root : Bool
   field dirs : List String
   field file : Maybe String

record URL : Set where
   constructor mkURL
   
   field scheme : Maybe String
   field authority : Maybe Authority
   field drive : Maybe String
   field path-root : Bool
   field dirs : List String
   field file : Maybe String
   field query : Maybe String
   field fragment : Maybe String
   
   path : Path
   path = mkPath path-root dirs file
   
   -- field {scheme-valid} : maybe ValidScheme ⊤ scheme
   -- field {drive-valid} : maybe ValidDrive ⊤ drive

data Mode : Set where
   web-mode file-mode generic-mode : Mode

private
   -- Note: We know here that the list contains only decimal digits, and at least one.
   parse-port : List Char → ℕ
   parse-port [] = 0
   parse-port (x ∷ []) = (toℕ x ∸ 0x30)
   parse-port (x ∷ xs) = (toℕ x ∸ 0x30) * 10 + parse-port xs
   
   remove-leading-c0 : List Char → List Char
   remove-leading-c0 = dropWhile (_≤? '\x20')
   
   remove-trailing-c0 : List Char → List Char
   remove-trailing-c0 = reverse ∘ remove-leading-c0 ∘ reverse
   
   remove-tab-nl : List Char → List Char
   remove-tab-nl = filter λ s → ¬? (s ≟ᶜ '\t' and s ≟ᶜ '\r' and s ≟ᶜ '\n')
   
   pre : String → String
   pre = fromList ∘ remove-leading-c0 ∘ remove-trailing-c0 ∘ remove-tab-nl ∘ toList
   
   web-scheme-regex : Exp
   file-scheme-regex : Exp
   any-scheme-regex : Exp
   
   web-scheme-regex = foldr _∣_ ∅ $ map (foldr _∙_ ε ∘ map singleton ∘ toList) ("http:" ∷ "https:" ∷ "ws:" ∷ "wss:" ∷ "ftp:" ∷ [])
   file-scheme-regex = foldr _∙_  ε $ map singleton (toList "file:")
   any-scheme-regex = scheme-regex ∙ singleton ':'
   
   lowercase-ch : Char → Char
   lowercase-ch ch with 'A' ≤? ch and ch ≤? 'Z'
   ... | yes _ = fromℕ $ toℕ ch + 0x20
   ... | no _ = ch
   
   lowercase : String → String
   lowercase = fromList ∘ map lowercase-ch ∘ toList

parse′ : Mode → String → Maybe URL
parse′ mode′ input = Maybe.map proj₁ $ url str
   where
   
   str : String
   str = pre input
   
   mode- : List Char → Mode
   mode- str with Prefix.shortest str web-scheme-regex | Prefix.shortest str file-scheme-regex | Prefix.shortest str any-scheme-regex
   ... | yes _ | _ | _ = web-mode
   ... | _ | yes _ | _ = file-mode
   ... | _ | _ | yes _ = generic-mode
   ... | _ | _ | _ = mode′
   
   mode : Mode
   mode = mode- $ toList (lowercase str)
   
   s-chars- : Mode → List Char
   s-chars- mode with mode
   ... | generic-mode = '/' ∷ []
   ... | _ = '/' ∷ '\\' ∷ []
   
   s-chars : List Char
   s-chars = s-chars- mode
   
   s : Exp
   s = [ map [_] s-chars ]
   
   user-char = [^ map [_] $ s-chars ++ᴸ toList "#:?" ]
   host-char = [^ map [_] $ toList "x00\x09\x0A\x0D #/:<>?@[\\]^" ]
   path-char = [^ map [_] $ s-chars ++ᴸ toList "#?" ]
   query-char = [^ [ '#' ] ∷ [] ]
   
   scheme : Parser String
   scheme = do
      result ← longest scheme-regex
      single ':'
      return result
   
   path-root : Parser ⊤
   path-root = do
      longest s
      return tt
   
   PathRel : Set
   PathRel = List String × Maybe String
   
   PathAbs : Set
   PathAbs = Bool × PathRel
   
   PathDrive : Set
   PathDrive = Maybe String × PathAbs
   
   AuthorityPath : Set
   AuthorityPath = Maybe Authority × PathDrive
   
   path-rel : Parser PathRel
   path-rel = do
      path ← longest $ (path-char ⋆ ∙ s) ⋆
      file ← try ∘ longest $ path-char +
      let dirs = split (λ ch → fromList (ch ∷ []) is? s) $ toList path
      return $ map fromList dirs , file
   
   path-abs : Parser PathAbs
   path-abs = do
      path-root
      path ← path-rel
      return $ true , path
   
   path : Parser PathAbs
   path = do
      root ← try path-root
      path ← path-rel
      return $ is-just root , path
   
   password : Parser String
   password = do
      single ':'
      longest $ path-char ⋆
   
   credentials : Parser (String × Maybe String)
   credentials = do
      username ← longest $ user-char ⋆
      password ← try password
      single '@'
      return $ username , password
   
   port : Parser Port
   port = do
      port-name ← longest $ decimal +
      let portℕ = parse-port $ toList port-name
      port-valid ← assert (portℕ <? 2 ^ 16)
      return $ fromℕ< port-valid
   
   authority : Parser Authority
   authority = do
      credentials ← try credentials
      host ← longest $ host-char ⋆
      port ← try port
      let username , password = maybe′ (map₁ just) (nothing , nothing) credentials
      
      return record {
         username = username ;
         password = password ;
         host = just (opaque-host host) ;
         port = port }
   
   generic-auth-path : Parser AuthorityPath
   generic-auth-path = do
      longest s
      longest s
      authority ← authority
      path ← try path-abs
      return $ just authority , nothing , fromMaybe (false , [] , nothing) path
   
   drive : Parser (Maybe Authority × Maybe String)
   drive = do
      auth- ← try do longest s ; longest s
      try $ longest s
      drive ← longest drive-regex
      let auth = if is-just auth- then just $ mkAuthority nothing nothing nothing nothing else nothing
      return $ auth , just drive
   
   auth-drive : Parser (Maybe Authority × Maybe String)
   auth-drive = do
      longest s
      longest s
      host ← longest $ host-char ⋆
      drive ← try do
         longest s
         longest drive-regex
      
      return $ just record {
         username = nothing ;
         password = nothing ;
         host = just $ opaque-host host ;
         port = nothing } ,
         drive
   
   authority-drive : Parser (Maybe Authority × Maybe String)
   authority-drive = do
      auth-drive ← try auth-drive
      maybe return drive auth-drive
   
   file-auth-path : Parser AuthorityPath
   file-auth-path = do
      authority , drive ← authority-drive
      path ← try path-abs
      return $ authority , drive , fromMaybe (false , [] , nothing) path
   
   auth-path′ : Mode → Parser AuthorityPath
   auth-path′ file-mode = file-auth-path
   auth-path′ _ = generic-auth-path
   
   auth-path : Parser AuthorityPath
   auth-path =  auth-path′ mode
   
   authority-path : Parser AuthorityPath
   authority-path = do
      auth-path ← try auth-path
      flip (maybe return) auth-path do
         path ← path
         return $ nothing , nothing , path
   
   query : Parser String
   query = do
      single '?'
      longest $ query-char ⋆
   
   fragment : Parser String
   fragment = do
      single '#'
      longest $ · ⋆
   
   url : Parser URL
   url = do
      scheme ← try scheme
      authority , drive , path-root , dirs , file ← authority-path
      query ← try query
      fragment ← try fragment
      end
      
      return record {
         scheme = scheme ;
         authority = authority ;
         drive = drive ;
         path-root = path-root ;
         dirs = dirs ;
         file = file ;
         query = query ;
         fragment = fragment }

parse : String → Maybe URL
parse = parse′ generic-mode

private
   join : List String → String
   join = fromList ∘ concatMap toList

print-scheme : String → String
print-scheme = _++ ":"

print-host : Host → String
print-host (opaque-host string) = string
print-host _ = ""

print-authority : Authority → String
print-authority record { username = username ; password = password ; host = host } =
   "//" ++
   maybe (_++ maybe (":" ++_) "" password) "" username ++
   maybe print-host "" host

print-drive : String → String
print-drive = id

print-path-root : Bool → String
print-path-root true = "/"
print-path-root false = ""

print-dirs : List String → String
print-dirs = join ∘ map (_++ "/")

print-file : String → String
print-file = id

print-query : String → String
print-query = "?" ++_

print-fragment : String → String
print-fragment = "#" ++_

print-scheme′ : Maybe String → String
print-scheme′ = maybe print-scheme ""

print-authority′ : Maybe Authority → String
print-authority′ = maybe print-authority ""

print-drive′ : Maybe String → String
print-drive′ = maybe print-drive ""

print-file′ : Maybe String → String
print-file′ = maybe print-file ""

print-query′ : Maybe String → String
print-query′ = maybe print-query ""

print-fragment′ : Maybe String → String
print-fragment′ = maybe print-fragment ""

print : URL → String
print (mkURL scheme authority drive path-root dirs file query fragment) =
   print-scheme′ scheme ++
   print-authority′ authority ++
   print-drive′ drive ++
   print-path-root path-root ++
   print-dirs dirs ++
   print-file′ file ++
   print-query′ query ++
   print-fragment′ fragment

print-path : Path → String
print-path (mkPath path-root dirs file) =
   print-path-root path-root ++
   print-dirs dirs ++
   print-file′ file

open URL using (scheme ; authority ; drive ; path-root ; dirs ; file ; query ; fragment ; path) public
