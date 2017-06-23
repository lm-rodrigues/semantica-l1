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
        UOP operator expressionOne ->
            unaryOperationTypeInfer typeEnvironment operator expressionOne

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


unaryOperationTypeInfer : TypeEnvironment -> UnaryOperator -> Expression -> Maybe Type
unaryOperationTypeInfer typeEnvironment operator expressionOne =
    let
        expressionOneType =
            internalTypeInfer typeEnvironment expressionOne
    in
        case ( operator, expressionOneType ) of
            ( NOT, Just TBOOL ) ->
                Just TBOOL

            _ ->
                Nothing


binaryOperationTypeInfer : TypeEnvironment -> Expression -> BinaryOperator -> Expression -> Maybe Type
binaryOperationTypeInfer typeEnvironment expressionOne operator expressionTwo =
    let
        expressionOneType =
            internalTypeInfer typeEnvironment expressionOne

        expressionTwoType =
            internalTypeInfer typeEnvironment expressionTwo

        isNumericOperation =
            isValidNumericOperation expressionOneType expressionTwoType

        isBooleanOperation =
            isValidBooleanOperation expressionOneType expressionTwoType

        isComparisonOperation =
            isBooleanOperation || isNumericOperation
    in
        case operator of
            SUM ->
                if isNumericOperation then
                    Just TINT
                else
                    Nothing

            DIFF ->
                if isNumericOperation then
                    Just TINT
                else
                    Nothing

            MULT ->
                if isNumericOperation then
                    Just TINT
                else
                    Nothing

            DIV ->
                if isNumericOperation then
                    Just TINT
                else
                    Nothing

            LEQ ->
                if isNumericOperation then
                    Just TBOOL
                else
                    Nothing

            S.LT ->
                if isNumericOperation then
                    Just TBOOL
                else
                    Nothing

            GEQ ->
                if isNumericOperation then
                    Just TBOOL
                else
                    Nothing

            S.GT ->
                if isNumericOperation then
                    Just TBOOL
                else
                    Nothing

            S.EQ ->
                if isComparisonOperation then
                    Just TBOOL
                else
                    Nothing

            NEQ ->
                if isComparisonOperation then
                    Just TBOOL
                else
                    Nothing

            AND ->
                if isBooleanOperation then
                    Just TBOOL
                else
                    Nothing

            OR ->
                if isBooleanOperation then
                    Just TBOOL
                else
                    Nothing


isBooleanExpression : Maybe Type -> Bool
isBooleanExpression expressionType =
    expressionType == Just TBOOL


isValidBooleanOperation : Maybe Type -> Maybe Type -> Bool
isValidBooleanOperation expressionOneType expressionTwoType =
    (isBooleanExpression expressionOneType)
        && (isBooleanExpression expressionTwoType)


isNumericExpression : Maybe Type -> Bool
isNumericExpression expressionType =
    expressionType == Just TINT


isValidNumericOperation : Maybe Type -> Maybe Type -> Bool
isValidNumericOperation expressionOneType expressionTwoType =
    (isNumericExpression expressionOneType)
        && (isNumericExpression expressionTwoType)
