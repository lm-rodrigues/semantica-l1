module Syntax exposing (..)

{-| Provides the basic elements of Syntax of Typed L1.
-}


type Type
    = Tint
    | Tbool
    | Ty FunctionType


type alias FunctionType =
    ( Type, Type )


type Operator
    = Sum
    | Diff
    | Mult
    | Eq
    | Leq
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
    = ENum Int
    | EBool Int
    | Bop Expression Operator Expression
    | If Expression Expression Expression
    | Var Variable
    | App Expression Expression
    | Lam Function
    | Let Function Expression
    | Lrec Variable FunctionType Function Expression
