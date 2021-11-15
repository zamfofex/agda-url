module Data.URL where

open import Data.String using (String ; toList ; fromList ; _++_) renaming (_≟_ to _≟ˢ_)
open import Data.Nat using (ℕ ; _^_ ; _<?_ ; _+_ ; _∸_ ; _*_) renaming (_≟_ to _≟ᴺ_)
open import Data.Fin using (Fin ; fromℕ<)
open import Data.Empty using (⊥)
open import Data.Bool using (Bool ; true ; false ; if_then_else_ ; _∨_ ; T ; T?)
open import Data.Char using (Char ; toℕ ; fromℕ ; _≤?_) renaming (_≟_ to _≟ᶜ_)
open import Data.Char.Properties using (≤-decPoset)
open import Text.Regex ≤-decPoset
   using (Exp ; Match ; [_] ; [^_] ; _─_ ; _∣_ ; _∙_ ; _⋆ ; _+ ; · ; singleton ; ε ; ∅)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Data.List
   using (List ; _∷_ ; [] ; drop ; map ; length ; concatMap ; dropWhile ; reverse ; filter ; foldr ; head)
   renaming (linesBy to split ; _++_ to _++ᴸ_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.DecPropositional _≟ˢ_ using () renaming (_∈?_ to _∈?ˢ_)
open import Text.Regex.Search ≤-decPoset using (module Whole ; module Prefix)
open import Relation.Binary using () renaming (Decidable to Decidable₂)
open import Data.Maybe as Maybe using (Maybe ; maybe ; maybe′ ; fromMaybe ; just ; nothing ; is-just ; Is-just ; to-witness)
open import Data.Maybe.Relation.Unary.Any using (just)
open import Function using (_∘_ ; _∘′_ ; _$_ ; _$′_ ; flip ; id ; const ; case_of_)
open import Data.Unit using (⊤ ; tt) renaming (_≟_ to _≟ᵁ_)
open import Category.Monad.State using (StateT ; StateTMonad)
open import Data.Product as Σ using (_,_ ; _,′_ ; map₁ ; proj₁ ; _×_)
open import Category.Monad using (RawMonad)
open import Data.Maybe.Categorical as Maybe using ()
open RawMonad (StateTMonad String Maybe.monad) using (_>>=_ ; _>>_ ; return)
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Nullary.Product using () renaming (_×-dec_ to _and_)
open import Relation.Nullary.Sum using () renaming (_⊎-dec_ to _or_)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Unary using (Decidable)

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
   
   _is?_ : Decidable₂ _::_
   _is?_ = Whole.search ∘ toList
   
   -- Simple monad for parsing strings.
   
   Parser : Set → Set
   Parser = StateT String Maybe
   
   try : ∀ {A} → Parser A → Parser (Maybe A)
   try f str = maybe (just ∘′ map₁ just) (just $′ nothing , str) (f str)
   
   assert : ∀ {A} → Dec A → Parser A
   assert (yes p) = return p
   assert (no _) = const nothing
   
   end : Parser ⊤
   end str with length (toList str) ≟ᴺ 0
   ... | yes _ = just $′ tt , ""
   ... | no _ = nothing
   
   -- Parsing operations based on regexes.
   
   -- TODO: Preserve the match proof somehow.
   -- TODO: Maybe by adding a variant that drops it,
   -- TODO: in order to avoid sacrificing convenience of usage for simple cases.
   longest : Exp → Parser String
   longest exp str with Prefix.longest (toList str) exp
   ... | yes match = just $′ fromList list-match , (fromList $ drop (length list-match) (toList str))
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
   
   module AuthorityParser (s-chars : List Char) where
      
      user-char host-char path-char query-char : Exp
      user-char = [^ map [_] $ s-chars ++ᴸ toList "#:?" ]
      host-char = [^ map [_] $ toList "x00\x09\x0A\x0D #/:<>?@[\\]^" ]
      path-char = [^ map [_] $ s-chars ++ᴸ toList "#?" ]
      query-char = [^ [ '#' ] ∷ [] ]
      
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
      
      authority-parser : Parser Authority
      authority-parser = do
         credentials ← try credentials
         host ← longest $ host-char ⋆
         port ← try port
         let username , password = maybe′ (map₁ just) (nothing , nothing) credentials
         
         return record {
            username = username ;
            password = password ;
            host = just (opaque-host host) ;
            port = port }
      
      parse-authority : String → Maybe Authority
      parse-authority str = Maybe.map proj₁ $ authority-parser- str
         where
         authority-parser- : Parser Authority
         authority-parser- = do
            authority ← authority-parser
            end
            return authority
   
   web-schemes : List String
   web-schemes = "http" ∷ "https" ∷ "ws" ∷ "wss" ∷ "ftp" ∷ []
   
   web-scheme-regex : Exp
   file-scheme-regex : Exp
   any-scheme-regex : Exp
   
   web-scheme-regex = foldr _∣_ ∅ $ map (foldr _∙_ ε ∘ map singleton ∘ toList ∘ (_++ ":")) web-schemes
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
   
   open AuthorityParser s-chars
   
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
   
   generic-auth-path : Parser AuthorityPath
   generic-auth-path = do
      longest s
      longest s
      authority ← authority-parser
      path ← try path-abs
      return $ just authority , nothing , fromMaybe (false , [] , nothing) path
   
   drive : Parser (Maybe Authority × Maybe String)
   drive = do
      auth- ← try do longest s ; longest s
      try $ longest s
      drive ← longest drive-regex
      let auth = if is-just auth- then just $′ mkAuthority nothing nothing nothing nothing else nothing
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
         host = just $′ opaque-host host ;
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
   is-just? : ∀ {a} {A : Set a} → Decidable (Is-just {A = A})
   is-just? nothing = no λ ()
   is-just? (just x) = yes (just tt)

record AbsoluteURL url : Set where
   field has-scheme : Is-just (URL.scheme url)
   scheme : String
   scheme = to-witness has-scheme

record WebURL url : Set where
   field absolute : AbsoluteURL url
   open AbsoluteURL absolute using (scheme) public
   field web-scheme : lowercase scheme ∈ web-schemes

record FileURL url : Set where
   field absolute : AbsoluteURL url
   open AbsoluteURL absolute using (scheme) public
   field file-scheme : lowercase scheme ≡ "file"

record BaseWebURL url : Set where
   field web-url : WebURL url
   field has-root : T (URL.path-root url)
   field has-authority : Is-just (URL.authority url)
   
   authority : Authority
   authority = to-witness has-authority
   
   field has-host : Is-just (Authority.host authority)
   
   host : Host
   host = to-witness has-host
   
   open WebURL web-url using (scheme) public

record BaseFileURL url : Set where
   field file-url : FileURL url
   field has-authority : Is-just (URL.authority url)
   field has-root : T (URL.path-root url) ⊎ Is-just (URL.drive url)
   
   authority : Authority
   authority = to-witness has-authority
   
   open FileURL file-url using (scheme) public

record BaseGenericURL url : Set where
   field absolute : AbsoluteURL url
   field has-root : Is-just (URL.authority url) ⊎ T (URL.path-root url)
   
   open AbsoluteURL absolute using (scheme) public
   scheme-equal : scheme ≡ (AbsoluteURL.scheme absolute)
   scheme-equal = refl

data BaseURL url : Set where
   web-base-url : BaseWebURL url → BaseURL url
   file-base-url : BaseFileURL url → BaseURL url
   generic-base-url : BaseGenericURL url → BaseURL url

absolute-urls-unique : ∀ {url} (a b : AbsoluteURL url) → a ≡ b
absolute-urls-unique record { has-scheme = just tt } record { has-scheme = just tt } = refl

-- TODO
postulate web-urls-unique : ∀ {url} (a b : WebURL url) → a ≡ b
postulate file-urls-unique : ∀ {url} (a b : FileURL url) → a ≡ b
postulate base-web-urls-unique : ∀ {url} (a b : BaseWebURL url) → a ≡ b
postulate base-file-urls-unique : ∀ {url} (a b : BaseFileURL url) → a ≡ b
postulate base-generic-urls-unique : ∀ {url} (a b : BaseGenericURL url) → a ≡ b
postulate base-urls-unique : ∀ {url} (a b : BaseURL url) → a ≡ b

absolute-url? : Decidable AbsoluteURL
absolute-url? url with is-just? $ URL.scheme url
... | yes has-scheme = yes record { has-scheme = has-scheme }
... | no not-has-scheme = no λ where record { has-scheme = has-scheme } → not-has-scheme has-scheme

web-url? : Decidable WebURL
web-url? url with absolute-url? url
... | no not-absolute = no λ where record { absolute = absolute } → not-absolute absolute
... | yes absolute with lowercase (AbsoluteURL.scheme absolute) ∈?ˢ web-schemes
... | no not-web-scheme = no λ where record { absolute = absolute₂ ; web-scheme = web-scheme } → case absolute-urls-unique absolute absolute₂ of λ where refl → not-web-scheme web-scheme
... | yes web-scheme = yes record { absolute = absolute ; web-scheme = web-scheme }

file-url? : Decidable FileURL
file-url? url with absolute-url? url
... | no not-absolute = no λ (record { absolute = absolute }) → not-absolute absolute
... | yes absolute with lowercase (AbsoluteURL.scheme absolute) ≟ˢ "file"
... | no not-file-scheme = no λ where record { absolute = absolute₂ ; file-scheme = file-scheme } → case absolute-urls-unique absolute absolute₂ of λ where refl → not-file-scheme file-scheme
... | yes file-scheme = yes record { absolute = absolute ; file-scheme = file-scheme }

base-web-url? : Decidable BaseWebURL
base-web-url? url with web-url? url
base-web-url? _ | no not-web-url = no λ where record { web-url = web-url } → not-web-url web-url
base-web-url? record { path-root = false } | yes _ = no λ ()
base-web-url? record { authority = nothing } | yes _ = no λ ()
base-web-url? record { authority = just record { host = just _ } ; path-root = true } | yes web-url = yes record { web-url = web-url ; has-authority = just _ ; has-host = just _ }
base-web-url? record { authority = just record { host = nothing } } | yes _ = no p where postulate p : _ -- TODO

base-file-url? : Decidable BaseFileURL
base-file-url? url with file-url? url
base-file-url? _ | no not-file-url = no λ where record { file-url = file-url } → not-file-url file-url
base-file-url? record { path-root = false ; drive = nothing } | yes _ = no λ where record { has-root = inj₁ () } ; record { has-root = inj₂ () }
base-file-url? record { authority = nothing } | yes _ = no λ ()
base-file-url? record { authority = just _ ; path-root = true } | yes file-url = yes record { file-url = file-url ; has-root = inj₁ _ ; has-authority = just _ }
base-file-url? record { authority = just _ ; drive = just _ } | yes file-url = yes record { file-url = file-url ; has-root = inj₂ $ just tt ; has-authority = just _ }

base-generic-url? : Decidable BaseGenericURL
base-generic-url? url with absolute-url? url
... | no not-absolute = no λ where record { absolute = absolute } → not-absolute absolute
... | yes absolute with url
... | record { authority = just _ } = yes record { absolute = absolute ; has-root = inj₁ $ just tt }
... | record { path-root = true } = yes record { absolute = absolute ; has-root = inj₂ _ }
... | record { authority = nothing ; path-root = false } = no λ where record { has-root = inj₁ () } ; record { has-root = inj₂ () }

base-url? : Decidable BaseURL
base-url? url with base-web-url? url | base-file-url? url | base-generic-url? url
... | yes base-web-url | _ | _ = yes $ web-base-url base-web-url
... | _ | yes base-file-url | _ = yes $ file-base-url base-file-url
... | _ | _ | yes base-generic-url = yes $ generic-base-url base-generic-url
... | no not-base-web-url | no not-base-file-url | no not-base-generic-url = no λ where
   (web-base-url base-web-url) → not-base-web-url base-web-url
   (file-base-url base-file-url) → not-base-file-url base-file-url
   (generic-base-url base-generic-url) → not-base-generic-url base-generic-url

private
   first-nonempty-part : URL → Maybe String
   first-nonempty-part record { dirs = dirs ; file = file } = head ∘ filter (λ str → ¬? (str ≟ˢ "")) $ dirs ++ᴸ fromMaybe "" file ∷ []

force : URL → Maybe URL
force url with absolute-url? url
... | no _ = nothing
... | yes _ with file-url? url | web-url? url | url
... | no _ | no _ | _ = nothing
... | yes _ | _ | record { drive = drive ; authority = authority ; path-root = path-root } =
   just record url { path-root = path-root ∨ ⌊ is-just? drive ⌋ ; authority = authority Maybe.<∣> (just $′ mkAuthority nothing nothing nothing nothing) }
... | _ | yes _ | record { authority = just _ } = just record url { path-root = true }
... | _ | yes _ | _ with first-nonempty-part url
... | nothing = nothing
... | just part with AuthorityParser.parse-authority (toList "/\\") part
... | nothing = nothing
... | just authority = just record url { path-root = true ; authority = just authority }

_goto_ : URL → URL → URL
url₁ goto url₂ with url₂
... | record { scheme = just _ } = url₂
... | record { authority = just _ } = record url₂ { scheme = scheme }
   where open URL url₁ using (scheme)
... | record { drive = just _ } = record url₂ { scheme = scheme ; authority = authority }
   where open URL url₁ using (scheme ; authority)
... | record { path-root = true } = record url₂ { scheme = scheme ; authority = authority ; drive = drive }
   where open URL url₁ using (scheme ; authority ; drive)
... | record { dirs = _ ∷ _ } = record url₁ { file = file ; query = query ; fragment = fragment ; dirs = URL.dirs url₁ ++ᴸ URL.dirs url₂ }
   where open URL url₂ using (file ; query ; fragment)
... | record { file = just _ } = record url₁ { file = file ; query = query ; fragment = fragment }
   where open URL url₂ using (file ; query ; fragment)
... | record { query = just _ } = record url₁ { query = query ; fragment = fragment }
   where open URL url₂ using (query ; fragment)
... | record { } = record url₁ { fragment = fragment }
   where open URL url₂ using (fragment)

resolve : URL → URL → Maybe URL
resolve url₁ url₂ with base-url? url₂ or absolute-url? url₁ | absolute-url? url₂ and is-just? (URL.fragment url₂) | url₂
... | yes _ | _ | _ = just $ url₂ goto url₁
... | _ | yes _ | record { scheme = nothing } = nothing
... | _ | yes _ | record { authority = nothing } = nothing
... | _ | yes _ | record { drive = nothing } = nothing
... | _ | yes _ | record { path-root = false } = nothing
... | _ | yes _ | record { dirs = [] } = nothing
... | _ | yes _ | record { file = nothing } = nothing
... | _ | yes _ | record { query = nothing } = nothing
... | _ | yes _ | record { } = just $ url₂ goto url₁
... | _ | _ | _ = nothing

~resolve : URL → URL → Maybe URL
~resolve url₁ url₂ = resolve ~url₁ url₂
   where
   
   ~url₁- : Maybe String → Maybe String → URL
   ~url₁- (just scheme₁) (just scheme₂) = if ⌊ scheme₁ ≟ˢ scheme₂ ⌋ then record url₁ { scheme = nothing } else url₁
   ~url₁- _ _ = url₁
   
   ~url₁ : URL
   ~url₁ = ~url₁- (URL.scheme url₁) (URL.scheme url₂)

forced-resolve : URL → URL → Maybe URL
forced-resolve url₁ url₂ with web-url? url₂ or file-url? url₂
... | yes _ = Maybe._>>=_ (Maybe._>>=_ (force url₂) (~resolve url₁)) force
... | _ = Maybe._>>=_ (resolve url₁ url₂) force

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
print-drive = "/" ++_

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
