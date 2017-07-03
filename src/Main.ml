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


(* ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; *)
(* ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; *)
(* Execute type inference and evaluation for some expressions. *)
		   
let eval expression = internalEval emptyEnv expression
let typeInfer expression = internalTypeInfer emptyEnv expression
					     
let factorial_generic num = (LETREC
			       ( "fat"
			       , TINT
			       , TINT
			       , "x"
			       , TINT
			       , (IF
				    ( (BOP
					 ( (VAR "x")
					 , EQ
					 , (ENUM 0)))
				    , (ENUM 1)
				    , (BOP
					 ( (VAR "x")
					 , MULT
					 , (APP
					      ( (VAR "fat")
					      , (BOP
						   ( (VAR "x")
						   , DIFF
						   , (ENUM 1)))))))))
			       , (APP
				    ( (VAR "fat")
				    , (ENUM num )))));;


let factorial_five = factorial_generic 5  
let factorial_five_eval = VNUM 120 = (eval factorial_five);;
let factorial_five_type = TINT = (typeInfer factorial_five);;
  
let fn_input = (FN ("x", TINT, (VAR "x")));;
let fn_eval = (Closure ("x", (VAR "x"), []) = eval fn_input);;
let fn_type = (TFN (TINT, TINT)) = typeInfer fn_input;;

let app_input = (APP ((FN ("x", TINT, (VAR "x"))), (ENUM 0)));;
let app_eval = (VNUM 0) = eval app_input;;
let app_type = TINT = typeInfer app_input;;

let not_input1 = (UOP (NOT, (EBOOL true)))  
let not_eval1 = (VBOOL false ) = eval not_input1;;
let not_type1 = TBOOL = typeInfer not_input1;;				     

let not_input2 = (UOP (NOT, (EBOOL true)))  
let not_eval2 = (VBOOL false ) = eval not_input2;;
let not_type2 = TBOOL = typeInfer not_input2;;
  
let and_input1 = (BOP ((EBOOL false), AND,  (EBOOL false)));;
let and_input2 = (BOP ((EBOOL false), AND,  (EBOOL true)));;
let and_input3 = (BOP ((EBOOL true), AND,  (EBOOL false)));;
let and_input4 = (BOP ((EBOOL true), AND,  (EBOOL true)));;    
let and_eval1 = (VBOOL false ) = eval and_input1;;
let and_eval2 = (VBOOL false ) = eval and_input2;;
let and_eval3 = (VBOOL false ) = eval and_input3;;
let and_eval4 = (VBOOL true ) = eval and_input4;;
let and_type1 = TBOOL = typeInfer and_input1;;
let and_type2 = TBOOL = typeInfer and_input2;;
let and_type3 = TBOOL = typeInfer and_input3;;
let and_type4 = TBOOL = typeInfer and_input4;;
  
  
Printf.printf "Fatorial (5) Eval: %B\n" factorial_five_eval;;
Printf.printf "Fatorial (5) Type: %B\n" factorial_five_type;;  

Printf.printf "Simple function Eval: %B\n" fn_eval;;
Printf.printf "Simple function Type: %B\n" fn_type;;

Printf.printf "Simple Application Eval: %B\n" app_eval;;
Printf.printf "Simple Application Type: %B\n" app_type;;

Printf.printf "Not expression Eval: %B %B\n" not_eval1 not_eval2;;
Printf.printf "Not expression Type: %B %B\n" not_type1 not_type2;;
		  
Printf.printf "And expression Eval: %B %B %B %B\n" and_eval1 and_eval2 and_eval3 and_eval4;;
Printf.printf "And expression Type: %B %B %B %B\n" and_type1 and_type2 and_type3 and_type4;;
