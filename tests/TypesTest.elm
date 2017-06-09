module TypesTest exposing (..)

import Expect
import Fuzz exposing (list, int, string)
import Syntax as S
import Syntax exposing (..)
import Test exposing (..)
import Types exposing (..)


suite : Test
suite =
    describe "Type System of L1"
        [ describe "Integers Type Check"
            [ test "Negative integer should return a valid type" <|
                \_ ->
                    Expect.equal (typeInfer (ENUM -1)) (Just TINT)
            , test "Number zero should return a valid type" <|
                \_ ->
                    Expect.equal (typeInfer (ENUM 0)) (Just TINT)
            , test "Positive interger should return a valid type" <|
                \_ ->
                    Expect.equal (typeInfer (ENUM 1)) (Just TINT)
            ]
        , describe "Booleans Type Check"
            [ test "True should return a valid type" <|
                \_ ->
                    Expect.equal (typeInfer (EBOOL True)) (Just TBOOL)
            , test "False should return a valid type" <|
                \_ ->
                    Expect.equal (typeInfer (EBOOL False)) (Just TBOOL)
            ]
        ]
