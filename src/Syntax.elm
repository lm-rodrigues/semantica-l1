module Syntax exposing (..)

import Environment exposing (Environment)


{-| Provides the basic elements of Syntax of Typed L1.
-}
type Type
    = TINT
    | TBOOL
    | TFN FunctionType


type alias FunctionType =
    ( Type, Type )


type Operator
    = SUM
    | DIFF
    | MULT
    | DIV
    | LEQ
    | LT
    | GEQ
    | GT
    | EQ
    | NEQ
    | AND
    | OR
    | NOT


type Value
    = VNUM Int
    | VBOOL Bool
    | Closure Variable Expression (Environment Variable Value)
    | RClosure Variable Variable Expression (Environment Variable Value)


type alias Variable =
    String


type alias Function =
    ( Variable, Type, Expression )


type Expression
    = ENUM Int
    | EBOOL Bool
    | BOP Expression Operator Expression
    | VAR Variable
    | IF Expression Expression Expression
    | APP Expression Expression
    | FN Function
    | LET Function Expression
    | LETREC Variable FunctionType Function Expression



-- ENUM
-- EBOOL
-- VAR
-- IF
-- APP
-- FN
-- LET
-- LETREC
