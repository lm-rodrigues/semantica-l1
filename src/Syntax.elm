module Syntax exposing (..)

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
    = Vnum Int
    | Vbool Bool
    | Closure Variable Expression Envinroment
    | RClosure Variable Variable Expression Envinroment


type Envinroment
    = List ( Variable, Value )


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
