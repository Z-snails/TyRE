module Data.Regex.CommonRegexes

import Data.Regex

import Data.String
import Data.List
import Data.Maybe

||| Simple email regex
export
email : TyRE (String, String, String)
email =
    let firstPart : TyRE String
        firstPart = rh "`({}|({}|[%\\+_\\.-]))+`" [letter, digit]
        secondPart : TyRE String
        secondPart = joinBy "." . forget <$> sepBy1 (r ".") (rh "`({}|{})+`" [letter, digit])
        domain : TyRE String
        domain = fastPack `map` repFromTo 2 6 letter
    in rh "{}@{}.{}" [firstPart, secondPart, domain]

---password validation
data PasswordValidationError    = NoDigit
                                | NoCapitalLetter
                                | NoLowerCaseLetter
                                | NoSpecialCharacter
                                | ContainsSpace

passwordStrength : List ((TyRE (), PasswordValidationError))
passwordStrength =
    let hasDigit := ignore $ r ".*[0-9].*"
        hasCapitalLetter := ignore $ r ".*[A-Z].*"
        hasLowerCaseLetter := ignore $ r ".*[a-z].*"
        hasSpecialCharacter := ignore $ r "[@#$<>%^&:=,_\\*\\+\\.\\?\\-\\!]"
        doesntHaveSpaces := ignore $ rep0 $ predicate (/= ' ')
    in  [ (hasDigit, NoDigit)
        , (hasCapitalLetter, NoCapitalLetter)
        , (hasLowerCaseLetter, NoLowerCaseLetter)
        , (hasSpecialCharacter, NoSpecialCharacter)
        , (doesntHaveSpaces, ContainsSpace)
        ]

||| Strong password validation
export
validatePasswordSecurity : String -> List PasswordValidationError
validatePasswordSecurity str =
    passwordStrength >>= f where
        f : (TyRE (), PasswordValidationError) -> List PasswordValidationError
        f (tyre, error) = if match tyre str then [] else [error]

--- url
namespace UrlRegex
    export
    record URL where
        constructor HTTP
        isSSL : Maybe Bool
        domain : List1 String
        path : List String
        query : Maybe (List1 (String, String))
        fragment : Maybe String

    export
    Show URL where
        show (HTTP isSSL domain path query fragment) =
            let protocol :=
                    case isSSL of
                        Nothing => ""
                        (Just True) => "https://"
                        (Just False) => "http://"
                domainPart = joinBy "." $ forget domain
                pathPart := joinBy "/" path
                queryPart := joinBy "&" . (map (\(p, v) => p ++ "=" ++ v)) . forget <$> query
            in protocol ++ domainPart ++ pathPart ++ fromMaybe "" queryPart ++ fromMaybe "" fragment

    export
    url : TyRE URL
    url = (\(pr, h, p, q, f) => HTTP pr h p q f)
          <$> rh "{}?{}{}(\\?{})?(#{})?" [protocol, domain, path, query, fragment]
      where
        urlSafeChar : TyRE Char
        urlSafeChar = digitChar `or` letter `or` oneOfChars "_-"

        protocol : TyRE Bool
        protocol = const False <$> r "http://"
            `or` const True <$> r "https://"

        domain : TyRE (List1 String)
        domain = sepBy1 (r ".") (rh "`({}|{})+`" [letter, digit])

        path : TyRE (List String)
        path = rh "(/`{}`)*" [urlSafeChar]

        query : TyRE (List1 (String, String))
        query = rh "(`{}+`=`{}+`)+" [urlSafeChar, urlSafeChar]

        fragment : TyRE String
        fragment = rh "`{}+`" [urlSafeChar]
