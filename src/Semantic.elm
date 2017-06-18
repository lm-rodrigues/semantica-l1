module Semantic exposing (eval)

import Environment exposing (..)
import Syntax as S
import Syntax exposing (..)
import Types exposing (..)


type alias Env =
    Environment Variable Value


eval : Expression -> Maybe Value
eval expression =
    internalEval emptyEnv expression


internalEval : Env -> Expression -> Maybe Value
internalEval environment expression =
    case expression of
        ENUM number ->
            Just <| VNUM number

        EBOOL boolean ->
            Just <| VBOOL boolean

        UOP operator expressionOne ->
            unaryOperationEval environment operator expressionOne

        BOP expressionOne operator expressionTwo ->
            binaryOperationEval environment expressionOne operator expressionTwo

        VAR variable ->
            envLookup variable environment

        IF condition thenExpression elseExpression ->
            ifEval environment condition thenExpression elseExpression

        APP function argument ->
            appEval environment function argument

        FN ( variable, _, expression ) ->
            Just <| Closure variable expression environment

        LET function expression ->
            letEval environment function expression

        LETREC variable _ function expression ->
            letRecEval environment variable function expression


unaryOperationEval : Env -> UnaryOperator -> Expression -> Maybe Value
unaryOperationEval environment operator expressionOne =
    let
        expressionOneEval =
            internalEval environment expressionOne
    in
        case operator of
            NOT ->
                case expressionOneEval of
                    Just (VBOOL valueOne) ->
                        Just <| VBOOL (not valueOne)

                    _ ->
                        Nothing


binaryOperationEval : Env -> Expression -> BinaryOperator -> Expression -> Maybe Value
binaryOperationEval environment expressionOne operator expressionTwo =
    let
        expressionOneEval =
            internalEval environment expressionOne

        expressionTwoEval =
            internalEval environment expressionTwo
    in
        case operator of
            SUM ->
                case ( expressionOneEval, expressionTwoEval ) of
                    ( Just (VNUM valueOne), Just (VNUM valueTwo) ) ->
                        Just <| VNUM (valueOne + valueTwo)

                    _ ->
                        Nothing

            DIFF ->
                case ( expressionOneEval, expressionTwoEval ) of
                    ( Just (VNUM valueOne), Just (VNUM valueTwo) ) ->
                        Just <| VNUM (valueOne - valueTwo)

                    _ ->
                        Nothing

            MULT ->
                case ( expressionOneEval, expressionTwoEval ) of
                    ( Just (VNUM valueOne), Just (VNUM valueTwo) ) ->
                        Just <| VNUM (valueOne * valueTwo)

                    _ ->
                        Nothing

            DIV ->
                case ( expressionOneEval, expressionTwoEval ) of
                    ( Just (VNUM valueOne), Just (VNUM valueTwo) ) ->
                        Just <| VNUM (valueOne // valueTwo)

                    _ ->
                        Nothing

            S.LT ->
                case ( expressionOneEval, expressionTwoEval ) of
                    ( Just (VNUM valueOne), Just (VNUM valueTwo) ) ->
                        Just <| VBOOL (valueOne < valueTwo)

                    _ ->
                        Nothing

            S.LEQ ->
                case ( expressionOneEval, expressionTwoEval ) of
                    ( Just (VNUM valueOne), Just (VNUM valueTwo) ) ->
                        Just <| VBOOL (valueOne <= valueTwo)

                    _ ->
                        Nothing

            S.GT ->
                case ( expressionOneEval, expressionTwoEval ) of
                    ( Just (VNUM valueOne), Just (VNUM valueTwo) ) ->
                        Just <|
                            VBOOL
                                (valueOne > valueTwo)

                    _ ->
                        Nothing

            S.GEQ ->
                case ( expressionOneEval, expressionTwoEval ) of
                    ( Just (VNUM valueOne), Just (VNUM valueTwo) ) ->
                        Just <| VBOOL (valueOne >= valueTwo)

                    _ ->
                        Nothing

            S.EQ ->
                case ( expressionOneEval, expressionTwoEval ) of
                    ( Just (VNUM valueOne), Just (VNUM valueTwo) ) ->
                        Just <| VBOOL (valueOne == valueTwo)

                    ( Just (VBOOL valueOne), Just (VBOOL valueTwo) ) ->
                        Just <| VBOOL (valueOne == valueTwo)

                    _ ->
                        Nothing

            S.NEQ ->
                case ( expressionOneEval, expressionTwoEval ) of
                    ( Just (VNUM valueOne), Just (VNUM valueTwo) ) ->
                        Just <| VBOOL (valueOne == valueTwo)

                    ( Just (VBOOL valueOne), Just (VBOOL valueTwo) ) ->
                        Just <| VBOOL (valueOne == valueTwo)

                    _ ->
                        Nothing

            S.AND ->
                case ( expressionOneEval, expressionTwoEval ) of
                    ( Just (VBOOL valueOne), Just (VBOOL valueTwo) ) ->
                        Just <| VBOOL (valueOne && valueTwo)

                    _ ->
                        Nothing

            S.OR ->
                case ( expressionOneEval, expressionTwoEval ) of
                    ( Just (VBOOL valueOne), Just (VBOOL valueTwo) ) ->
                        Just <| VBOOL (valueOne || valueTwo)

                    _ ->
                        Nothing


ifEval : Env -> Expression -> Expression -> Expression -> Maybe Value
ifEval environment condition thenCase elseCase =
    let
        conditionEval =
            internalEval environment condition

        thenCaseEval =
            internalEval environment thenCase

        elseCaseEval =
            internalEval environment elseCase
    in
        case conditionEval of
            Just (VBOOL True) ->
                thenCaseEval

            Just (VBOOL False) ->
                elseCaseEval

            _ ->
                Nothing


appEval : Env -> Expression -> Expression -> Maybe Value
appEval environment function argument =
    let
        functionEval =
            internalEval environment function

        argumentEval =
            internalEval environment argument
    in
        case argumentEval of
            Just value ->
                case functionEval of
                    Just (Closure variable subExpression fnEnvironment) ->
                        internalEval
                            (insertEnv variable value fnEnvironment)
                            subExpression

                    Just (RClosure recVariable fnVariable subExpression fnEnvironment) ->
                        let
                            recClosure =
                                RClosure recVariable fnVariable subExpression fnEnvironment
                        in
                            internalEval
                                (insertEnv fnVariable value <|
                                    insertEnv recVariable recClosure <|
                                        fnEnvironment
                                )
                                subExpression

                    _ ->
                        Nothing

            _ ->
                Nothing


letEval : Env -> Function -> Expression -> Maybe Value
letEval environment ( variable, _, subExpression ) expression =
    let
        subExpressionEval =
            internalEval environment subExpression
    in
        case subExpressionEval of
            Just value ->
                internalEval
                    (insertEnv variable value environment)
                    expression

            _ ->
                Nothing


letRecEval : Env -> Variable -> Function -> Expression -> Maybe Value
letRecEval environment recVariable ( fnVariable, _, subExpression ) expression =
    let
        recursiveEnvironment =
            insertEnv
                recVariable
                (RClosure recVariable fnVariable subExpression environment)
                environment
    in
        internalEval recursiveEnvironment expression
