module Types exposing (typeInfer)

import Environment exposing (..)
import Syntax as S
import Syntax exposing (..)


type alias TypeEnvironment =
    Environment Variable Type


typeInfer : Expression -> Maybe Type
typeInfer expression =
    internalTypeInfer emptyEnv expression


internalTypeInfer : TypeEnvironment -> Expression -> Maybe Type
internalTypeInfer typeEnvironment expression =
    case expression of
        BOP expressionOne operator expressionTwo ->
            binaryOperationTypeInfer typeEnvironment expressionOne operator expressionTwo

        ENUM _ ->
            Just TINT

        EBOOL _ ->
            Just TBOOL

        VAR variable ->
            envLookup variable typeEnvironment

        IF booleanExpression expressionOne expressionTwo ->
            ifTypeInfer typeEnvironment booleanExpression expressionOne expressionTwo

        APP function argument ->
            appTypeInfer typeEnvironment function argument

        FN function ->
            functionTypeInfer typeEnvironment function

        LET function expression ->
            letTypeInfer typeEnvironment function expression

        LETREC recursiveFunction recursiveFunctionType recursiveFunctionExpression expression ->
            letRecTypeInfer typeEnvironment recursiveFunction recursiveFunctionType recursiveFunctionExpression expression


ifTypeInfer : TypeEnvironment -> Expression -> Expression -> Expression -> Maybe Type
ifTypeInfer typeEnvironment condition thenCase elseCase =
    let
        conditionInfer =
            internalTypeInfer typeEnvironment condition

        thenCaseInfer =
            internalTypeInfer typeEnvironment thenCase

        elseCaseInfer =
            internalTypeInfer typeEnvironment elseCase
    in
        case ( conditionInfer, thenCaseInfer, elseCaseInfer ) of
            ( Just TBOOL, Just thenCaseType, Just elseCaseType ) ->
                if thenCaseType == elseCaseType then
                    Just thenCaseType
                else
                    Nothing

            _ ->
                Nothing


appTypeInfer : TypeEnvironment -> Expression -> Expression -> Maybe Type
appTypeInfer typeEnvironment function argument =
    let
        functionInfer =
            internalTypeInfer typeEnvironment function

        argumentInfer =
            internalTypeInfer typeEnvironment argument
    in
        case ( functionInfer, argumentInfer ) of
            ( Just (TFN ( inputType, returnType )), Just argumentType ) ->
                if argumentType == inputType then
                    Just returnType
                else
                    Nothing

            _ ->
                Nothing


functionTypeInfer : TypeEnvironment -> Function -> Maybe Type
functionTypeInfer typeEnvironment ( variable, variableType, subExpression ) =
    let
        newTypeEnvironment =
            insertEnv variable variableType typeEnvironment
    in
        case internalTypeInfer newTypeEnvironment subExpression of
            Just subExpressionType ->
                Just <| TFN ( variableType, subExpressionType )

            _ ->
                Nothing


letTypeInfer : TypeEnvironment -> Function -> Expression -> Maybe Type
letTypeInfer typeEnvironment ( variable, variableType, expressionOne ) expressionTwo =
    let
        newTypeEnvironment =
            insertEnv variable variableType typeEnvironment
    in
        case internalTypeInfer typeEnvironment expressionOne of
            Just expressionOneType ->
                internalTypeInfer newTypeEnvironment expressionTwo

            Nothing ->
                Nothing


letRecTypeInfer : TypeEnvironment -> Variable -> FunctionType -> Function -> Expression -> Maybe Type
letRecTypeInfer typeEnvironment recursiveFunction ( inputType, outputType ) ( variable, variableType, subExpression ) expressionTwo =
    let
        subExpressionTypeEnvironment =
            insertEnv variable variableType <|
                insertEnv recursiveFunction (TFN ( inputType, outputType )) <|
                    typeEnvironment

        expressionTwoEnvironmentType =
            insertEnv recursiveFunction (TFN ( inputType, outputType )) <|
                typeEnvironment
    in
        case internalTypeInfer subExpressionTypeEnvironment subExpression of
            Just subExpressionType ->
                if inputType == variableType && subExpressionType == outputType then
                    internalTypeInfer expressionTwoEnvironmentType expressionTwo
                else
                    Nothing

            _ ->
                Nothing


binaryOperationTypeInfer : TypeEnvironment -> Expression -> Operator -> Expression -> Maybe Type
binaryOperationTypeInfer typeEnvironment expressionOne operator expressionTwo =
    let
        expressionOneType =
            internalTypeInfer typeEnvironment expressionOne

        expressionTwoType =
            internalTypeInfer typeEnvironment expressionTwo

        numericOperationsType =
            isValidNumericOperation expressionOneType expressionTwoType

        booleanOperationsType =
            isValidBooleanOperation expressionOneType expressionTwoType

        comparisonOperations =
            if isBooleanExpression expressionOneType then
                isValidBooleanOperation expressionOneType expressionTwoType
            else if isNumericExpression expressionOneType then
                isValidNumericOperation expressionOneType expressionTwoType
            else
                Nothing
    in
        case operator of
            SUM ->
                numericOperationsType

            DIFF ->
                numericOperationsType

            MULT ->
                numericOperationsType

            DIV ->
                numericOperationsType

            LEQ ->
                numericOperationsType

            S.LT ->
                numericOperationsType

            GEQ ->
                numericOperationsType

            S.GT ->
                numericOperationsType

            S.EQ ->
                comparisonOperations

            NEQ ->
                comparisonOperations

            AND ->
                booleanOperationsType

            OR ->
                booleanOperationsType

            NOT ->
                booleanOperationsType


isBooleanExpression : Maybe Type -> Bool
isBooleanExpression expressionType =
    expressionType == Just TBOOL


isValidBooleanOperation : Maybe Type -> Maybe Type -> Maybe Type
isValidBooleanOperation expressionOneType expressionTwoType =
    if
        (isBooleanExpression expressionOneType)
            && (isBooleanExpression expressionTwoType)
    then
        Just TBOOL
    else
        Nothing


isNumericExpression : Maybe Type -> Bool
isNumericExpression expressionType =
    expressionType == Just TINT


isValidNumericOperation : Maybe Type -> Maybe Type -> Maybe Type
isValidNumericOperation expressionOneType expressionTwoType =
    if
        (isNumericExpression expressionOneType)
            && (isNumericExpression expressionTwoType)
    then
        Just TINT
    else
        Nothing
