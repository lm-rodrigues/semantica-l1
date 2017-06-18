module Main exposing (..)

import Environment exposing (..)
import Html exposing (text)
import Semantic exposing (..)
import Syntax as S
import Syntax exposing (..)
import Types exposing (..)


main =
    text <| toString (eval test)


test =
    LETREC
        "fat"
        ( TINT, TINT )
        ( "x"
        , TINT
        , IF
            (BOP
                (VAR "x")
                S.EQ
                (ENUM 0)
            )
            (ENUM 1)
            (BOP
                (VAR "x")
                MULT
                (APP
                    (VAR "fat")
                    (BOP
                        (VAR "x")
                        DIFF
                        (ENUM 1)
                    )
                )
            )
        )
        (APP
            (VAR "fat")
            (ENUM 0)
        )
