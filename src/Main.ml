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

			   
exception BadTypedExpression

            
let isBooleanExpression expressionType =
  expressionType = TBOOL

let isValidBooleanOperation expressionOneType expressionTwoType =
  (isBooleanExpression expressionOneType)
  && (isBooleanExpression expressionTwoType)
     
let isNumericExpression expressionType =
  expressionType = TINT
		     
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
     raise BadTypedExpression

let rec internalTypeInfer typeEnvironment expression =
  match expression with
  | UOP (operator, expressionOne) ->
     let unaryOperationTypeInfer typeEnvironment operator expressionOne =
       match ( operator, internalTypeInfer typeEnvironment expressionOne ) with
       | ( NOT, TBOOL ) ->
          TBOOL
            
       | _ ->
          raise BadTypedExpression
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
     let varTypeInfer variable =
     try envLookup variable typeEnvironment with
       KeyNotInEnvironment -> raise BadTypedExpression
     in
     varTypeInfer variable
	       
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
          raise BadTypedExpression
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
          raise BadTypedExpression
     in appTypeInfer typeEnvironment functionExpression argument

		     
  | FN (variable, variableType, subExpression) ->       
     let
       newTypeEnvironment = insertEnv variable variableType typeEnvironment
     in
     TFN ( variableType, internalTypeInfer newTypeEnvironment subExpression )
	 
  | LET (variable, variableType, expressionOne, expressionTwo) ->
     let letTypeInfer typeEnvironment ( variable, variableType, expressionOne, expressionTwo ) =
       let
	 expressionOneType = internalTypeInfer typeEnvironment expressionOne
       and
	 newTypeEnvironment = insertEnv variable variableType typeEnvironment
       in
       match expressionOneType with
       | _ when (expressionOneType = variableType) ->
          internalTypeInfer newTypeEnvironment expressionTwo

       | _ ->
	  raise BadTypedExpression
			    
     in letTypeInfer typeEnvironment (variable, variableType, expressionOne, expressionTwo)

		     
  | LETREC (recursiveFunction, inputType, outputType, subExpressionVariable, subExpressionType, subExpression, expression) ->
     let letRecTypeInfer typeEnvironment recursiveFunction inputType outputType variable variableType subExpression expressionTwo =
       let
         subExpressionTypeEnvironment =
	 insertEnv variable variableType ( insertEnv recursiveFunction (TFN ( inputType, outputType )) typeEnvironment)
       and
         expressionTwoEnvironmentType =
	 insertEnv recursiveFunction (TFN ( inputType, outputType )) typeEnvironment
       in
       match internalTypeInfer subExpressionTypeEnvironment subExpression with
       | subExpressionType when
              inputType = variableType && subExpressionType = outputType ->
          internalTypeInfer expressionTwoEnvironmentType expressionTwo
			    
       | _ ->
          raise BadTypedExpression

     in letRecTypeInfer
	  typeEnvironment recursiveFunction inputType outputType
	  subExpressionVariable subExpressionType subExpression expression



(* ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; *)
(* ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; *)
(* Provides the operational semantic for the language *)        
exception NotValidUnaryExpression
exception NotValidBinaryExpression
exception NotValidIFExpression
exception NotValidAppExpression
exception NotValidLetExpression

let binaryOperationEval operator expressionOneEval expressionTwoEval =
  match ( operator, expressionOneEval, expressionTwoEval ) with
  | (SUM, VNUM valueOne, VNUM valueTwo ) ->
     VNUM (valueOne + valueTwo)
	  
  | (DIFF, VNUM valueOne, VNUM valueTwo ) ->
     VNUM (valueOne - valueTwo)
	  
  | (MULT, VNUM valueOne, VNUM valueTwo ) ->
     VNUM (valueOne * valueTwo)
	  
  | (DIV, VNUM valueOne, VNUM valueTwo )
       when valueTwo != 0 ->
     VNUM (valueOne / valueTwo)

  | (DIV, VNUM _, VNUM valueTwo )
       when valueTwo = 0 ->
     VNUM 0
	   
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
       | ( NOT, VBOOL value) ->
	  let notEval value =
	    match value with
	    | true ->
	       VBOOL false
	    | false ->
	       VBOOL true
	  in
	  notEval value
		
       | _ ->
          raise NotValidUnaryExpression
     in 
     unaryOperationEval environment operator expressionOne


			
  | BOP (expressionOne, operator, expressionTwo) ->
     let binaryOperationShortCircuit expressionOne expressionTwo =
       let expressionOneEval = internalEval environment expressionOne
       and expressionTwoEval = internalEval environment expressionTwo
       in
       match operator with
       | AND ->
	  let andEval expressionOneEval expressionTwoEval =
	    match (expressionOneEval) with
	    | (VBOOL true) ->
	       expressionTwoEval
		     
	    | (VBOOL false) ->
	       VBOOL false

	    | _ ->
	       raise NotValidBinaryExpression
	  in
	  andEval expressionOneEval expressionTwoEval

		  
       | OR ->
	  let orEval expressionOneEval expressionTwoEval =
	    match (expressionOneEval) with
	    | (VBOOL false) ->
	       expressionTwoEval
		
	    | (VBOOL true) ->
	       VBOOL true
		     
	    | _ ->
	       raise NotValidBinaryExpression
	  in
	  orEval expressionOneEval expressionTwoEval

		 
       | _ ->
	  binaryOperationEval operator expressionOneEval expressionTwoEval
     in
     binaryOperationShortCircuit expressionOne expressionTwo


				 
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
            (insertEnv fnVariable value (insertEnv recVariable recClosure fnEnvironment)) subExpression
            
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
         insertEnv recVariable (RClosure (recVariable, fnVariable, subExpression, environment)) environment
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
let factorial_five_eval = VNUM 120 = eval factorial_five;;
let factorial_five_type = TINT = typeInfer factorial_five;;

Printf.printf "Fatorial (5) Eval: %B\n" factorial_five_eval;;
Printf.printf "Fatorial (5) Type: %B\n\n" factorial_five_type;;  


  
let fn_input = FN ("x", TINT, (VAR "x"));;
let fn_eval = Closure ("x", (VAR "x"), []) = eval fn_input;;
let fn_type = TFN (TINT, TINT) = typeInfer fn_input;;

Printf.printf "Simple function Eval: %B\n" fn_eval;;
Printf.printf "Simple function Type: %B\n\n" fn_type;;



let let_input = LET ("y", TFN(TINT,TINT), (FN ("x", TINT, (VAR "x"))), (APP ((VAR "y"), (ENUM 0))));;
let let_eval = VNUM 0 = eval let_input;;
let let_type = TINT = typeInfer let_input;;

Printf.printf "Simple Let Eval: %B\n" let_eval;;
Printf.printf "Simple Let Type: %B\n\n" let_type;;
  
  
let app_input = APP ((FN ("x", TINT, (VAR "x"))), (ENUM 0));;
let app_eval = VNUM 0 = eval app_input;;
let app_type = TINT = typeInfer app_input;;

Printf.printf "Simple Application Eval: %B\n" app_eval;;
Printf.printf "Simple Application Type: %B\n\n" app_type;;


  
let not_input1 = UOP (NOT, (EBOOL true));;  
let not_input2 = UOP (NOT, (EBOOL false));;  
let not_eval1 = VBOOL false = eval not_input1;;
let not_eval2 = VBOOL true  = eval not_input2;;
let not_type1 = TBOOL = typeInfer not_input1;;				     
let not_type2 = TBOOL = typeInfer not_input2;;

Printf.printf "Not expression Eval: %B %B\n" not_eval1 not_eval2;;
Printf.printf "Not expression Type: %B %B\n\n" not_type1 not_type2;;


  
let and_input1 = BOP ((EBOOL false), AND,  (EBOOL false));;
let and_input2 = BOP ((EBOOL false), AND,  (EBOOL true));;
let and_input3 = BOP ((EBOOL true), AND,  (EBOOL false));;
let and_input4 = BOP ((EBOOL true), AND,  (EBOOL true));;    
let and_eval1 = VBOOL false = eval and_input1;;
let and_eval2 = VBOOL false = eval and_input2;;
let and_eval3 = VBOOL false = eval and_input3;;
let and_eval4 = VBOOL true  = eval and_input4;;
let and_type1 = TBOOL = typeInfer and_input1;;
let and_type2 = TBOOL = typeInfer and_input2;;
let and_type3 = TBOOL = typeInfer and_input3;;
let and_type4 = TBOOL = typeInfer and_input4;;

Printf.printf "And expression Eval: %B %B %B %B\n" and_eval1 and_eval2 and_eval3 and_eval4;;
Printf.printf "And expression Type: %B %B %B %B\n\n" and_type1 and_type2 and_type3 and_type4;;


  
let or_input1 = BOP ((EBOOL false), OR,  (EBOOL false));;
let or_input2 = BOP ((EBOOL false), OR,  (EBOOL true));;
let or_input3 = BOP ((EBOOL true), OR,  (EBOOL false));;
let or_input4 = BOP ((EBOOL true), OR,  (EBOOL true));;    
let or_eval1 = VBOOL false = eval or_input1;;
let or_eval2 = VBOOL true  = eval or_input2;;
let or_eval3 = VBOOL true  = eval or_input3;;
let or_eval4 = VBOOL true  = eval or_input4;;
let or_type1 = TBOOL = typeInfer or_input1;;
let or_type2 = TBOOL = typeInfer or_input2;;
let or_type3 = TBOOL = typeInfer or_input3;;
let or_type4 = TBOOL = typeInfer or_input4;;

Printf.printf "Or expression Eval: %B %B %B %B\n" or_eval1 or_eval2 or_eval3 or_eval4;;
Printf.printf "Or expression Type: %B %B %B %B\n\n" or_type1 or_type2 or_type3 or_type4;;


  
let sum_input1 = BOP ((ENUM 0), SUM,  (ENUM 0));;
let sum_input2 = BOP ((ENUM 1), SUM,  (ENUM 0));;
let sum_input3 = BOP ((ENUM 0), SUM,  (ENUM 1));;
let sum_input4 = BOP ((ENUM 1), SUM,  (ENUM 1));;
let sum_input5 = BOP ((ENUM (-1)), SUM,  (ENUM 0));;
let sum_input6 = BOP ((ENUM 0), SUM,  (ENUM (-1)));;
let sum_input7 = BOP ((ENUM (-1)), SUM,  (ENUM (-1)));;
let sum_eval1 = VNUM 0 = eval sum_input1;;
let sum_eval2 = VNUM 1 = eval sum_input2;;
let sum_eval3 = VNUM 1 = eval sum_input3;;
let sum_eval4 = VNUM 2 = eval sum_input4;;
let sum_eval5 = VNUM (-1) = eval sum_input5;;
let sum_eval6 = VNUM (-1) = eval sum_input6;;
let sum_eval7 = VNUM (-2) = eval sum_input7;;  
let sum_type1 = TINT = typeInfer sum_input1;;
let sum_type2 = TINT = typeInfer sum_input2;;
let sum_type3 = TINT = typeInfer sum_input3;;
let sum_type4 = TINT = typeInfer sum_input4;;
let sum_type5 = TINT = typeInfer sum_input5;;
let sum_type6 = TINT = typeInfer sum_input6;;
let sum_type7 = TINT = typeInfer sum_input7;;

Printf.printf "Sum expression Eval: %B %B %B %B %B %B %B \n" sum_eval1 sum_eval2 sum_eval3 sum_eval4 sum_eval5 sum_eval6 sum_eval7;;
Printf.printf "Sum expression Type: %B %B %B %B %B %B %B \n\n" sum_type1 sum_type2 sum_type3 sum_type4 sum_type5 sum_type6 sum_type7;;  

  

let diff_input1 = BOP ((ENUM 0), DIFF,  (ENUM 0));;
let diff_input2 = BOP ((ENUM 1), DIFF,  (ENUM 0));;
let diff_input3 = BOP ((ENUM 0), DIFF,  (ENUM 1));;
let diff_input4 = BOP ((ENUM 1), DIFF,  (ENUM 1));;
let diff_input5 = BOP ((ENUM (-1)), DIFF,  (ENUM 0));;
let diff_input6 = BOP ((ENUM 0), DIFF,  (ENUM (-1)));;
let diff_input7 = BOP ((ENUM (-1)), DIFF,  (ENUM (-1)));;
let diff_eval1 = VNUM 0 = eval diff_input1;;
let diff_eval2 = VNUM 1 = eval diff_input2;;
let diff_eval3 = VNUM (-1) = eval diff_input3;;
let diff_eval4 = VNUM 0 = eval diff_input4;;
let diff_eval5 = VNUM (-1) = eval diff_input5;;
let diff_eval6 = VNUM 1 = eval diff_input6;;
let diff_eval7 = VNUM 0 = eval diff_input7;;
let diff_type1 = TINT = typeInfer diff_input1;;
let diff_type2 = TINT = typeInfer diff_input2;;
let diff_type3 = TINT = typeInfer diff_input3;;
let diff_type4 = TINT = typeInfer diff_input4;;
let diff_type5 = TINT = typeInfer diff_input5;;
let diff_type6 = TINT = typeInfer diff_input6;;
let diff_type7 = TINT = typeInfer diff_input7;;

Printf.printf "Diff expression Eval: %B %B %B %B %B %B %B \n" diff_eval1 diff_eval2 diff_eval3 diff_eval4 diff_eval5 diff_eval6 diff_eval7;;
Printf.printf "Diff expression Type: %B %B %B %B %B %B %B \n\n" diff_type1 diff_type2 diff_type3 diff_type4 diff_type5 diff_type6 diff_type7;;  


  
let div_input1 = BOP ((ENUM 0), DIV,  (ENUM 0));;
let div_input2 = BOP ((ENUM 1), DIV,  (ENUM 0));;
let div_input3 = BOP ((ENUM 0), DIV,  (ENUM 1));;
let div_input4 = BOP ((ENUM 1), DIV,  (ENUM 1));;
let div_input5 = BOP ((ENUM (-1)), DIV,  (ENUM 0));;
let div_input6 = BOP ((ENUM 0), DIV,  (ENUM (-1)));;
let div_input7 = BOP ((ENUM (-1)), DIV,  (ENUM (-1)));;
let div_input8 = BOP ((ENUM 3), DIV,  (ENUM 2));;
let div_eval1 = VNUM 0 = eval div_input1;;
let div_eval2 = VNUM 0 = eval div_input2;;
let div_eval3 = VNUM 0 = eval div_input3;;
let div_eval4 = VNUM 1 = eval div_input4;;
let div_eval5 = VNUM 0 = eval div_input5;;
let div_eval6 = VNUM 0 = eval div_input6;;
let div_eval7 = VNUM 1 = eval div_input7;;
let div_eval8 = VNUM 1 = eval div_input8;;  
let div_type1 = TINT = typeInfer div_input1;;
let div_type2 = TINT = typeInfer div_input2;;
let div_type3 = TINT = typeInfer div_input3;;
let div_type4 = TINT = typeInfer div_input4;;
let div_type5 = TINT = typeInfer div_input5;;
let div_type6 = TINT = typeInfer div_input6;;
let div_type7 = TINT = typeInfer div_input7;;
let div_type8 = TINT = typeInfer div_input8;;
  
Printf.printf "Div expression Eval: %B %B %B %B %B %B %B %B \n" div_eval1 div_eval2 div_eval3 div_eval4 div_eval5 div_eval6 div_eval7 div_eval8;;
Printf.printf "Div expression Type: %B %B %B %B %B %B %B %B \n\n" div_type1 div_type2 div_type3 div_type4 div_type5 div_type6 div_type7 div_type8;;  


  
let mult_input1 = BOP ((ENUM 0), MULT,  (ENUM 0));;
let mult_input2 = BOP ((ENUM 1), MULT,  (ENUM 0));;
let mult_input3 = BOP ((ENUM 0), MULT,  (ENUM 1));;
let mult_input4 = BOP ((ENUM 1), MULT,  (ENUM 1));;
let mult_input5 = BOP ((ENUM (-1)), MULT,  (ENUM 0));;
let mult_input6 = BOP ((ENUM 0), MULT,  (ENUM (-1)));;
let mult_input7 = BOP ((ENUM (-1)), MULT,  (ENUM (-1)));;
let mult_input8 = BOP ((ENUM 1), MULT,  (ENUM (-1)));;
let mult_input9 = BOP ((ENUM (-1)), MULT,  (ENUM 1));;
let mult_eval1 = VNUM 0 = eval mult_input1;;
let mult_eval2 = VNUM 0 = eval mult_input2;;
let mult_eval3 = VNUM 0 = eval mult_input3;;
let mult_eval4 = VNUM 1 = eval mult_input4;;
let mult_eval5 = VNUM 0 = eval mult_input5;;
let mult_eval6 = VNUM 0 = eval mult_input6;;
let mult_eval7 = VNUM 1 = eval mult_input7;;
let mult_eval8 = VNUM (-1) = eval mult_input8;;
let mult_eval9 = VNUM (-1) = eval mult_input9;;
let mult_type1 = TINT = typeInfer mult_input1;;
let mult_type2 = TINT = typeInfer mult_input2;;
let mult_type3 = TINT = typeInfer mult_input3;;
let mult_type4 = TINT = typeInfer mult_input4;;
let mult_type5 = TINT = typeInfer mult_input5;;
let mult_type6 = TINT = typeInfer mult_input6;;
let mult_type7 = TINT = typeInfer mult_input7;;
let mult_type8 = TINT = typeInfer mult_input8;;
let mult_type9 = TINT = typeInfer mult_input9;;

  
Printf.printf "Mult expression Eval: %B %B %B %B %B %B %B %B %B \n" mult_eval1 mult_eval2 mult_eval3 mult_eval4 mult_eval5 mult_eval6 mult_eval7 mult_eval8 mult_eval9;;
Printf.printf "Mult expression Type: %B %B %B %B %B %B %B %B %B \n\n" mult_type1 mult_type2 mult_type3 mult_type4 mult_type5 mult_type6 mult_type7 mult_type8 mult_type9;;  


  
let lt_input1 = BOP ((ENUM 0), LT,  (ENUM 0));;
let lt_input2 = BOP ((ENUM 1), LT,  (ENUM 0));;
let lt_input3 = BOP ((ENUM 0), LT,  (ENUM 1));;
let lt_eval1 = VBOOL false = eval lt_input1;;
let lt_eval2 = VBOOL false = eval lt_input2;;
let lt_eval3 = VBOOL true  = eval lt_input3;;
let lt_type1 = TBOOL = typeInfer lt_input1;;
let lt_type2 = TBOOL = typeInfer lt_input2;;
let lt_type3 = TBOOL = typeInfer lt_input3;;

Printf.printf "LT expression Eval: %B %B %B \n" lt_eval1 lt_eval2 lt_eval3;;
Printf.printf "LT expression Type: %B %B %B \n\n" lt_type1 lt_type2 lt_type3;;



let leq_input1 = BOP ((ENUM 0), LEQ,  (ENUM 0));;
let leq_input2 = BOP ((ENUM 1), LEQ,  (ENUM 0));;
let leq_input3 = BOP ((ENUM 0), LEQ,  (ENUM 1));;
let leq_eval1 = VBOOL true  = eval leq_input1;;
let leq_eval2 = VBOOL false = eval leq_input2;;
let leq_eval3 = VBOOL true  = eval leq_input3;;
let leq_type1 = TBOOL = typeInfer leq_input1;;
let leq_type2 = TBOOL = typeInfer leq_input2;;
let leq_type3 = TBOOL = typeInfer leq_input3;;

Printf.printf "LEQ expression Eval: %B %B %B \n" leq_eval1 leq_eval2 leq_eval3;;
Printf.printf "LEQ expression Type: %B %B %B \n\n" leq_type1 leq_type2 leq_type3;;      



let gt_input1 = BOP ((ENUM 0), GT,  (ENUM 0));;
let gt_input2 = BOP ((ENUM 1), GT,  (ENUM 0));;
let gt_input3 = BOP ((ENUM 0), GT,  (ENUM 1));;
let gt_eval1 = VBOOL false = eval gt_input1;;
let gt_eval2 = VBOOL true = eval gt_input2;;
let gt_eval3 = VBOOL false = eval gt_input3;;
let gt_type1 = TBOOL = typeInfer gt_input1;;
let gt_type2 = TBOOL = typeInfer gt_input2;;
let gt_type3 = TBOOL = typeInfer gt_input3;;

Printf.printf "GT expression Eval: %B %B %B \n" gt_eval1 gt_eval2 gt_eval3;;
Printf.printf "GT expression Type: %B %B %B \n\n" gt_type1 gt_type2 gt_type3;;



let geq_input1 = BOP ((ENUM 0), GEQ,  (ENUM 0));;
let geq_input2 = BOP ((ENUM 1), GEQ,  (ENUM 0));;
let geq_input3 = BOP ((ENUM 0), GEQ,  (ENUM 1));;
let geq_eval1 = VBOOL true = eval geq_input1;;
let geq_eval2 = VBOOL true = eval geq_input2;;
let geq_eval3 = VBOOL false = eval geq_input3;;
let geq_type1 = TBOOL = typeInfer geq_input1;;
let geq_type2 = TBOOL = typeInfer geq_input2;;
let geq_type3 = TBOOL = typeInfer geq_input3;;

Printf.printf "GEQ expression Eval: %B %B %B \n" geq_eval1 geq_eval2 geq_eval3;;
Printf.printf "GEQ expression Type: %B %B %B \n\n" geq_type1 geq_type2 geq_type3;;      
  


let eq_input1 = BOP ((ENUM 0), EQ,  (ENUM 0));;
let eq_input2 = BOP ((ENUM 1), EQ,  (ENUM 0));;
let eq_input3 = BOP ((ENUM 0), EQ,  (ENUM 1));;
let eq_input4 = BOP ((ENUM 1), EQ,  (ENUM 1));;  
let eq_input5 = BOP ((EBOOL true), EQ,  (EBOOL true));;
let eq_input6 = BOP ((EBOOL true), EQ,  (EBOOL false));;
let eq_input7 = BOP ((EBOOL false), EQ,  (EBOOL true));;
let eq_input8 = BOP ((EBOOL false), EQ,  (EBOOL false));;  
let eq_eval1 = VBOOL true  = eval eq_input1;;
let eq_eval2 = VBOOL false = eval eq_input2;;
let eq_eval3 = VBOOL false = eval eq_input3;;
let eq_eval4 = VBOOL true  = eval eq_input4;;
let eq_eval5 = VBOOL true  = eval eq_input5;;
let eq_eval6 = VBOOL false = eval eq_input6;;
let eq_eval7 = VBOOL false = eval eq_input7;;
let eq_eval8 = VBOOL true  = eval eq_input8;;
let eq_type1 = TBOOL = typeInfer eq_input1;;
let eq_type2 = TBOOL = typeInfer eq_input2;;
let eq_type3 = TBOOL = typeInfer eq_input3;;
let eq_type4 = TBOOL = typeInfer eq_input4;;
let eq_type5 = TBOOL = typeInfer eq_input5;;  
let eq_type6 = TBOOL = typeInfer eq_input6;;
let eq_type7 = TBOOL = typeInfer eq_input7;;
let eq_type8 = TBOOL = typeInfer eq_input8;;

Printf.printf "EQ expression Eval: %B %B %B %B %B %B %B %B \n" eq_eval1 eq_eval2 eq_eval3 eq_eval4 eq_eval5 eq_eval6 eq_eval7 eq_eval8;;
Printf.printf "EQ expression Type: %B %B %B %B %B %B %B %B \n\n" eq_type1 eq_type2 eq_type3 eq_type4 eq_type5 eq_type6 eq_type7 eq_type8;;   
  


let neq_input1 = BOP ((ENUM 0), NEQ,  (ENUM 0));;
let neq_input2 = BOP ((ENUM 1), NEQ,  (ENUM 0));;
let neq_input3 = BOP ((ENUM 0), NEQ,  (ENUM 1));;
let neq_input4 = BOP ((ENUM 1), NEQ,  (ENUM 1));;  
let neq_input5 = BOP ((EBOOL true), NEQ,  (EBOOL true));;
let neq_input6 = BOP ((EBOOL true), NEQ,  (EBOOL false));;
let neq_input7 = BOP ((EBOOL false), NEQ,  (EBOOL true));;
let neq_input8 = BOP ((EBOOL false), NEQ,  (EBOOL false));;  
let neq_eval1 = VBOOL false = eval neq_input1;;
let neq_eval2 = VBOOL true  = eval neq_input2;;
let neq_eval3 = VBOOL true  = eval neq_input3;;
let neq_eval4 = VBOOL false = eval neq_input4;;
let neq_eval5 = VBOOL false = eval neq_input5;;
let neq_eval6 = VBOOL true  = eval neq_input6;;
let neq_eval7 = VBOOL true  = eval neq_input7;;
let neq_eval8 = VBOOL false = eval neq_input8;;
let neq_type1 = TBOOL = typeInfer neq_input1;;
let neq_type2 = TBOOL = typeInfer neq_input2;;
let neq_type3 = TBOOL = typeInfer neq_input3;;
let neq_type4 = TBOOL = typeInfer neq_input4;;
let neq_type5 = TBOOL = typeInfer neq_input5;;  
let neq_type6 = TBOOL = typeInfer neq_input6;;
let neq_type7 = TBOOL = typeInfer neq_input7;;
let neq_type8 = TBOOL = typeInfer neq_input8;;

Printf.printf "NEQ expression Eval: %B %B %B %B %B %B %B %B \n" neq_eval1 neq_eval2 neq_eval3 neq_eval4 neq_eval5 neq_eval6 neq_eval7 neq_eval8;;
Printf.printf "NEQ expression Type: %B %B %B %B %B %B %B %B \n\n" neq_type1 neq_type2 neq_type3 neq_type4 neq_type5 neq_type6 neq_type7 neq_type8;;
  


let if_input1 = IF ((EBOOL true), (ENUM 1), (ENUM 0));;
let if_input2 = IF ((EBOOL false), (ENUM 1), (ENUM 0));;
let if_eval1 = VNUM 1 = eval if_input1;;
let if_eval2 = VNUM 0 = eval if_input2;;
let if_type1 = TINT = typeInfer if_input1;;
let if_type2 = TINT = typeInfer if_input2;;


Printf.printf "IF expression Eval: %B %B  \n" if_eval1 if_eval2;;
Printf.printf "IF expression Type: %B %B \n\n" if_type1 if_type2;;



let int_input1 = ENUM 0;;
let int_input2 = ENUM 1;;
let int_eval1 = VNUM 0 = eval int_input1;;
let int_eval2 = VNUM 1 = eval int_input2;;
let int_type1 = TINT = typeInfer int_input1;;
let int_type2 = TINT = typeInfer int_input2;;


Printf.printf "INT expression Eval: %B %B  \n" int_eval1 int_eval2;;
Printf.printf "INT expression Type: %B %B \n\n" int_type1 int_type2;;



let bool_input1 = EBOOL true;;
let bool_input2 = EBOOL false;;
let bool_eval1 = VBOOL true = eval bool_input1;;
let bool_eval2 = VBOOL false = eval bool_input2;;
let bool_type1 = TBOOL = typeInfer bool_input1;;
let bool_type2 = TBOOL = typeInfer bool_input2;;


Printf.printf "BOOL expression Eval: %B %B  \n" bool_eval1 bool_eval2;;
Printf.printf "BOOL expression Type: %B %B \n\n" bool_type1 bool_type2;;


let var_input = LET ("y", TFN(TINT,TINT), (FN ("x", TINT, (VAR "x"))), (VAR "y"));;
let var_eval = Closure ("x", (VAR "x"), []) = eval var_input;;
let var_type = TFN (TINT,TINT) = typeInfer var_input;;

Printf.printf "Simple Var Eval: %B\n" var_eval;;
Printf.printf "Simple Var Type: %B\n\n" var_type;;
