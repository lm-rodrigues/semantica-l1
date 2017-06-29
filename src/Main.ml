(* ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; *)
(* ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; *)
(* Provides the generic environment functions *)

type ('a, 'b) environment = ('a * 'b) list
                          
let emptyEnv =
  []

let insertEnv key value environment =
  ( key, value ) :: environment

exception KeyNotInEnvironment
        
let rec envLookup searchKey environment =
  match environment with
  | ( key, value ) :: xs ->
     if searchKey = key then
       value
     else
       envLookup searchKey xs
  | [] ->
     raise KeyNotInEnvironment
(* ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; *)
(* ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; *)
(* Provides the basic elements of Syntax of Typed L1. *)
     
type languageType =
  | TINT
  | TBOOL
  | TFN of languageType * languageType

         
type binaryOperator =
  | SUM
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

type unaryOperator =
  | NOT
  
type expression =
  | ENUM of int
  | EBOOL of bool
  | UOP of unaryOperator * expression
  | BOP of expression * binaryOperator * expression
  | VAR of string
  | IF of expression * expression * expression
  | APP of expression * expression
  | FN of string * languageType * expression
  | LET of string * languageType * expression * expression
  | LETREC of string * languageType * languageType * string * languageType * expression * expression
            
type value =
  | VNUM of int
  | VBOOL of bool
  | Closure of string * expression * (string, value) environment
  | RClosure of string * string * expression * (string, value) environment

(* ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; *)
(* ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; *)
(* Provides the type system for the language *)


type typeEnvironment =
  (string, languageType) environment         

  
exception BadTypeIfStatement
exception BadTypedAppStatement
exception BadTypedBinaryOperation
exception BadTypedUnaryOperation
exception BadTypedLetStatement        
exception BadTypedLetRecStatement

        
let isBooleanExpression expressionType =
  expressionType = TBOOL

(* isValidBooleanOperation : Maybe Type -> Maybe Type -> Bool *)
let isValidBooleanOperation expressionOneType expressionTwoType =
  (isBooleanExpression expressionOneType)
  && (isBooleanExpression expressionTwoType)
  
(* isNumericExpression : Maybe Type -> Bool*)
let isNumericExpression expressionType =
  expressionType = TINT
  
(* isValidNumericOperation : Maybe Type -> Maybe Type -> Bool *)
let isValidNumericOperation expressionOneType expressionTwoType =
  (isNumericExpression expressionOneType)
  && (isNumericExpression expressionTwoType)


let rec binaryOperationTypeInfer typeEnvironment expressionOneType operator expressionTwoType = 
  let isNumericOperation =
    isValidNumericOperation expressionOneType expressionTwoType
    
  and isBooleanOperation =
    isValidBooleanOperation expressionOneType expressionTwoType
  in 
  let isComparisonOperation =
    isBooleanOperation || isNumericOperation
  in
  match operator with
  | SUM when isNumericOperation ->
     TINT 

  | DIFF when isNumericOperation ->
     TINT

  | MULT when isNumericOperation ->
     TINT
    
  | DIV when isNumericOperation ->
     TINT
    
  | LEQ when isNumericOperation ->
     TBOOL
    
  | LT when isNumericOperation ->
     TBOOL
    
  | GEQ when isNumericOperation ->
     TBOOL
    
  | GT when isNumericOperation ->
     TBOOL
    
  | EQ when isComparisonOperation ->
     TBOOL
    
  | NEQ when isComparisonOperation ->
     TBOOL
    
  | AND when isBooleanOperation ->
     TBOOL
    
  | OR when isBooleanOperation ->
     TBOOL

  | _ ->
     raise BadTypedBinaryOperation

let rec internalTypeInfer typeEnvironment expression =
  match expression with
  | UOP (operator, expressionOne) ->
     let unaryOperationTypeInfer typeEnvironment operator expressionOne =
       match ( operator, internalTypeInfer typeEnvironment expressionOne ) with
       | ( NOT, TBOOL ) ->
          TBOOL
         
       | _ ->
          raise BadTypedUnaryOperation
     in 
     unaryOperationTypeInfer typeEnvironment operator expressionOne

     
  | BOP (expressionOne, operator, expressionTwo) ->
     let expressionOneType = internalTypeInfer typeEnvironment expressionOne
     and expressionTwoType = internalTypeInfer typeEnvironment expressionTwo
     in binaryOperationTypeInfer typeEnvironment expressionOneType operator expressionTwoType

      
  | ENUM _ ->
     TINT

    
  | EBOOL _ ->
     TBOOL

    
  | VAR variable ->
     envLookup variable typeEnvironment

    
  | IF (booleanExpression, expressionOne, expressionTwo) ->
     let ifTypeInfer typeEnvironment condition thenCase elseCase =
       match ( internalTypeInfer typeEnvironment condition
             , internalTypeInfer typeEnvironment thenCase
             , internalTypeInfer typeEnvironment elseCase
             ) with
       | ( TBOOL, thenCaseType, elseCaseType )
            when thenCaseType = elseCaseType ->
          thenCaseType
         
       | _ ->
          raise BadTypeIfStatement
     in
     ifTypeInfer
       typeEnvironment booleanExpression expressionOne expressionTwo

     
  | APP (functionExpression, argument) ->    
     let appTypeInfer typeEnvironment functionExpression argument =
       match ( internalTypeInfer typeEnvironment functionExpression
             , internalTypeInfer typeEnvironment argument ) with
       | (TFN ( inputType, returnType )), argumentType
            when argumentType = inputType ->
          returnType
       | _ ->
          raise BadTypedAppStatement
     in appTypeInfer typeEnvironment functionExpression argument

      
  | FN (variable, variableType, subExpression) ->       
     let
       newTypeEnvironment = insertEnv variable variableType typeEnvironment
     in
     TFN ( variableType, internalTypeInfer newTypeEnvironment subExpression )
     
  | LET (variable, variableType, expressionOne, expressionTwo) ->
     let letTypeInfer typeEnvironment ( variable, variableType, expressionOne, expressionTwo ) =
       let
         newTypeEnvironment = insertEnv variable variableType typeEnvironment
       in
       match internalTypeInfer typeEnvironment expressionOne with
       | _ ->
          internalTypeInfer newTypeEnvironment expressionTwo   
     in letTypeInfer typeEnvironment (variable, variableType, expressionOne, expressionTwo)

      
  | LETREC (recursiveFunction, inputType, outputType, subExpressionVariable, subExpressionType, subExpression, expression) ->
     let letRecTypeInfer typeEnvironment recursiveFunction inputType outputType variable variableType subExpression expressionTwo =
       let
         subExpressionTypeEnvironment = insertEnv variable variableType ( insertEnv recursiveFunction (TFN ( inputType, outputType )) typeEnvironment)
       and
         expressionTwoEnvironmentType = insertEnv recursiveFunction (TFN ( inputType, outputType )) typeEnvironment
       in
       match internalTypeInfer subExpressionTypeEnvironment subExpression with
       | subExpressionType when
              inputType = variableType && subExpressionType = outputType ->
          internalTypeInfer expressionTwoEnvironmentType expressionTwo
         
       | _ ->
          raise BadTypedLetRecStatement

     in letRecTypeInfer typeEnvironment recursiveFunction inputType outputType subExpressionVariable subExpressionType subExpression expression



(* ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; *)
(* ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; *)
(* Provides the operational semantic for the language *)        
exception NotValidUnaryExpression
exception NotValidBinaryExpression
exception NotValidIFExpression
exception NotValidAppExpression
exception NotValidLetExpression

let binaryOperationEval environment expressionOneEval operator expressionTwoEval =
  match ( operator, expressionOneEval, expressionTwoEval ) with
  | (SUM, VNUM valueOne, VNUM valueTwo ) ->
     VNUM (valueOne + valueTwo)
    
  | (DIFF, VNUM valueOne, VNUM valueTwo ) ->
     VNUM (valueOne - valueTwo)
    
  | (MULT, VNUM valueOne, VNUM valueTwo ) ->
     VNUM (valueOne * valueTwo)
    
  | (DIV, VNUM valueOne, VNUM valueTwo ) ->
     VNUM (valueOne / valueTwo)
    
  | (LT, VNUM valueOne, VNUM valueTwo ) ->
     VBOOL (valueOne < valueTwo)
    
  | (LEQ, VNUM valueOne, VNUM valueTwo ) ->
     VBOOL (valueOne <= valueTwo)

  | (GT, VNUM valueOne, VNUM valueTwo ) ->
     VBOOL (valueOne > valueTwo)
    
  | (GEQ, VNUM valueOne, VNUM valueTwo ) ->
     VBOOL (valueOne >= valueTwo)
    
  | (EQ, VNUM valueOne, VNUM valueTwo ) ->
     VBOOL (valueOne = valueTwo)

  | (EQ, VBOOL valueOne, VBOOL valueTwo) ->
     VBOOL (valueOne = valueTwo)
    
  | (NEQ, VNUM valueOne, VNUM valueTwo ) ->
     VBOOL (valueOne != valueTwo)
    
  | (NEQ, VBOOL valueOne, VBOOL valueTwo) ->
     VBOOL (valueOne != valueTwo)
    
  | (AND, VBOOL valueOne, VBOOL valueTwo) ->
     VBOOL (valueOne && valueTwo)
    
  | (OR, VBOOL valueOne, VBOOL valueTwo) ->
     VBOOL (valueOne || valueTwo)

  | _ ->
     raise NotValidBinaryExpression

    
let rec internalEval environment expression =
  match expression with
  | ENUM number ->
     VNUM number
    
  | EBOOL boolean ->
     VBOOL boolean

  | UOP (operator, expressionOne) ->
     let unaryOperationEval environment operator expressionOne =
       match ( operator, internalEval environment expressionOne ) with
       | ( NOT, VBOOL valueOne) ->
          VBOOL (not valueOne)
         
       | _ ->
          raise NotValidUnaryExpression
     in 
     unaryOperationEval environment operator expressionOne

  | BOP (expressionOne, operator, expressionTwo) ->
     let expressionOneEval = internalEval environment expressionOne
     and expressionTwoEval = internalEval environment expressionTwo
     in 
     binaryOperationEval environment expressionOneEval operator expressionTwoEval

  | VAR variable ->
     envLookup variable environment

  | IF (condition, thenExpression, elseExpression) ->
     let ifEval environment condition thenCase elseCase =
       match internalEval environment condition with
       | (VBOOL true) ->
          internalEval environment thenCase  
       | (VBOOL false) ->
          internalEval environment elseCase
         
       | _ ->
          raise NotValidIFExpression
     in
     ifEval environment condition thenExpression elseExpression

  | APP (languageFunction, argument) ->
     let appEval environment functioN argument =
       match ( internalEval environment languageFunction
             , internalEval environment argument
             ) with
       | (Closure (variable, subExpression, fnEnvironment), value ) ->
          internalEval  (insertEnv variable value fnEnvironment) subExpression
         
       | ( RClosure (recVariable, fnVariable, subExpression, fnEnvironment), value ) ->
          let
            recClosure = RClosure (recVariable, fnVariable, subExpression, fnEnvironment)
          in
          internalEval
            (insertEnv fnVariable value (insertEnv
                                           recVariable
                                           recClosure
                                           fnEnvironment))
            subExpression
          
       | _ ->
          raise NotValidAppExpression
     in appEval environment languageFunction argument

  | FN ( variable, _, expression ) ->
     Closure (variable, expression, environment)

  | LET (variable, inputType, subExpression, expression) ->
     let letEval environment ( variable, _, subExpression ) expression =
       match internalEval environment subExpression with
       | value ->
          internalEval
            (insertEnv variable value environment)
            expression
         
     in letEval environment (variable, inputType, subExpression) expression

  | LETREC (recursiveVariable, _, _, variable, inputType, subExpression, expression) ->
     let letRecEval environment recVariable ( fnVariable, _, subExpression ) expression =
       let
         recursiveEnvironment =
         insertEnv
           recVariable
           (RClosure (recVariable, fnVariable, subExpression, environment))
           environment
       in
       internalEval recursiveEnvironment expression
     in letRecEval environment recursiveVariable (variable, inputType, subExpression) expression
