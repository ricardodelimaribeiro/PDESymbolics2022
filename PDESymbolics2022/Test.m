(* Wolfram Language Package *)
(*BeginPackage["PDESymbolics2020`Test`"]*)
(*
$TestFunctions = 
 StringDrop[#, StringLength["Test"]] & /@ 
  Complement[Names["TestsPDESymbolics`Test*"], {"Test"}]
*)
$TestFunctions = {"MatrixKernelOperator", FindIntegratingFactorOperator, EqualToZeroOperator,
	"PiecewiseEliminateEqualitiesOperator",PiecewiseFullSimplifyOperator,"PiecewiseSimplifyOperator",
	"RegroupParametersOperator", FindConservedQuantityOperator, VarDOperator, DisintegrateOperator, 
	IntegrateByPartsOperator, BeautifyOperator, BasisModNullLagrangiansOperator, "BasisOperator"};

TestOperator::usage = "Traces evaluation and applies systematic tests to the intermediate computations."

TestVarDOperator::usage  ="Tests VarDOperator by comparing it to built-in variational derivative.";

TestDisintegrateOperator::usage  ="Tests DisintegrateOperator by checking that variational derivate of output and original expressions agree.";

TestIntegrateByPartsOperator::usage  ="Tests IntegrateByPartsOperator by checking that variational derivate of output and original expressions agree.";

TestBeautifyOperator::usage  ="Tests BeautifyOperator by checking that variational derivate of output and original expressions agree.";

TestBasisModNullLagrangiansOperator::usage = "Tests BasisModNullLagrangiansOperator by checking if it is an idempotent operation.";

TestBasisOperator::usage = "Tests BasisOperator by checking if it is an idempotent operation.";

TestFindConservedQuantityOperator::usage = "Tests FindConservedQuantity operator by checking if the time derivative of the quantity vanishes";

TestRegroupParametersOperator::usage = "Tests RegroupParametersOperator by checking that difference between the original form and the resulting form vanishes";

TestPiecewiseBeautify::usage ="checks if the output is equal to input";

TestPiecewiseSimplifyOperator::usage ="checks if the output is equal to input";

TestPiecewiseFullSimplifyOperator::usage ="checks if the output is equal to input";

TestPiecewiseEliminateEqualitiesOperator::usage ="checks if the output is equal to input";

TestEqualToZeroOperator::usage = "checks if the solution makes expression vanish";

TestFindIntegratingFactorOperator::usage = "checks if multiplying integrating factor makes expression a null Lagrangian";

TestMatrixKernelOperator::usage = "checks if all vectors in the output are part of the kernel";

Begin["`Private`"] (* Begin Private Context *) 

(* TESTS *)
(*TODO Kleisli for Tests!*)

TestMatrixKernelOperator[variables_, expression_, output_] :=
 Which[
  Head[expression] === Piecewise,
  True,
  Head[expression] === $Failed,
  output === $Failed,
  True,
  With[{
    check = (expression.# & /@ output) // Flatten // Expand
    },
   If[And @@ (# === 0 & /@ check), True, $Failed]]];

TestFindIntegratingFactorOperator[variables_, expression_, output_] :=
    Which[
   Head[expression] === Piecewise,
   True,
   Head[expression] === $Failed,
   output === $Failed,
   True, With[{check = 
      Lookup[variables, "VarDOperator", VarDOperator][variables][
         output.expression["expression"]] // Expand // Flatten}, 
    

If[
   	PiecewiseMap[(And@@Map[((# // Expand)===0)&, #])&, check]
    // PiecewiseExpand //
       PiecewiseSimplify // PiecewiseBeautify, True, $Failed]
   
    
    
    
    ]];



(*zeroq = (Head[#] =!= List && (# // Expand // Simplify) == 
      0) || (Head[#] === List && And @@ (zeroq /@ #)) &;*)

pretestEqualToZeroOperator[variables_, expression_, output_]:= Reduce[And @@ (Implies[#[[2]], zeroq[expression /. #[[1]]]] & /@ 
      output), Lookup[variables, "domain", Reals]];
      
TestEqualToZeroOperator=KleisliTest[pretestEqualToZeroOperator];



TestPiecewiseBeautifyOperator[variables_, expression_, output_] := 
  PiecewiseEqualOperator[variables][expression, output];



TestPiecewiseSimplifyOperator[variables_, expression_, output_] := 
  PiecewiseEqualOperator[variables][expression, output];
  
TestPiecewiseFullSimplifyOperator[variables_, expression_, output_] :=
PiecewiseEqualOperator[variables][expression, output];

TestPiecewiseEliminateEqualitiesOperator[variables_, 
   expression_, output_] :=
   PiecewiseEqualOperator[variables][expression, output];


TestRegroupParametersOperator[variables_, expression_, output_] :=  
  Which[
   Head[expression] === Piecewise, True,
   Head[expression] === $Failed, output === $Failed,
   True, With[{check = {(output - expression) // Expand//Simplify} // Flatten},
    If[And @@ (# === 0 & /@ check), True, $Failed]]];


TestFindConservedQuantityOperator[variables_, expression_, output_] :=
   Which[
   Head[expression] === Piecewise, True,
   Head[expression] === $Failed, output === $Failed,
   True,
   With[
   	{check=(Lookup[variables, "VarDOperator",VarDOperator][variables][
            TimeDerOperator[variables][output]])},
   If[
   	PiecewiseMap[(And@@Map[((# // Expand)===0)&, #])&, check]
    // PiecewiseExpand //
       PiecewiseSimplify // PiecewiseBeautify, True, $Failed]
   ]
   ];
   



TestBeautifyOperator[variables_, expression_, output_] :=
 Which[
  Head[expression] === List, True,
  Head[expression] === Piecewise, True,
  Head[expression] === $Failed, output === $Failed,
  True,
  Module[{localvariables,check},
  localvariables=Append[variables,"order"->1];
  check=(Lookup[variables, "VarDOperator", VarDOperator][
             variables][(expression - output) // PiecewiseExpand] // 
           PiecewiseSimplify // PiecewiseBeautify);
If[
   	PiecewiseMap[(And@@Map[((# // Expand)===0)&, #])&, check]
    // PiecewiseExpand //
       PiecewiseSimplify // PiecewiseBeautify, True, $Failed]
   ]
  ]


TestIntegrateByPartsOperator[variables_, expression_, output_] :=
 Which[
  Head[expression] === List, True,
  Head[expression] === Piecewise, True,
  Head[expression] === $Failed, output === $Failed,
  True,
  Module[{localvariables},
  	localvariables=Append[variables,"order"->1];
  If[(And @@ (# == 
          0 & /@ (Lookup[variables, "VarDOperator", VarDOperator][
             localvariables][(expression - output) // PiecewiseExpand] // 
           PiecewiseSimplify // PiecewiseBeautify))) === True, 
   True, $Failed]
  ]
  ]

TestDisintegrateOperator[variables_, expression_, output_] := 
 PiecewiseEqualOperator[variables][
  Lookup[variables, "VarDOperator", VarDOperator][variables][
   expression - output // PiecewiseExpand], 
  PiecewiseMap[
   If[# =!= $Failed, 
     Table[0, Length[Lookup[variables, "depVars", 0]]], $Failed] &, 
   expression]];

(*TestDisintegrateOperator[variables_, expression_, output_] :=
 Which[
  Head[expression] === List, True,
  Head[expression] === Piecewise, True,
  Head[expression] === $Failed, output === $Failed,
  True,
  If[(And @@ (# == 
          0 & /@ (Lookup[variables, "VarDOperator", VarDOperator][
             variables][expression - output // PiecewiseExpand] // 
           PiecewiseSimplify // PiecewiseBeautify))) === True, 
   True, $Failed]
  ]*)

TestBasisOperator[variables_, expression_, output_] :=
 Which[
  Head[expression] === Piecewise, True,
  Head[expression] === $Failed, output === $Failed,
  True, If[(BasisOperator[variables][expression] == output) // 
      PiecewiseExpand // PiecewiseSimplify // PiecewiseBeautify, 
   True, $Failed]];


(* tests if BasisModNullLagrangiansOperator  is idempotent *)

TestBasisModNullLagrangiansOperator[variables_, expression_, output_] :=
 Which[
  Head[expression] === Piecewise, True,
  Head[expression] === $Failed, output === $Failed,
  True, If[(BasisModNullLagrangiansOperator[variables][expression] == 
        output) // PiecewiseExpand // PiecewiseSimplify // 
    PiecewiseBeautify, True, $Failed]];


(*TestVarDOperator[variables_, expression_, output_] := 
With[
{
lhs=(output // Simplify // Expand),
rhs=(VariationalDOperator[variables][expression] // Simplify // Expand)
},
If[ lhs===rhs, True, $Failed]
];
      *)

TestVarDOperator[variables_, expression_, output_] :=
 Which[
  Head[expression] === List, True,
  Head[expression] === Piecewise, True,
  Head[expression] === $Failed, output === $Failed,
  True,
  With[{lhs = (output // Simplify // Expand), 
    rhs = (VariationalDOperator[variables][expression] // Simplify // 
       Expand)}, If[lhs === rhs, True, $Failed]]
  ]


(* ##########             function: traceParser           ########### \
*)
(**********************************************************************)
\
(* Purpose: From the output of Trace of wmma, traceParser extracts    \
*)
(*          all pairs of the form function call and function \
output   *)
(* Input:   unprocessed trace                             \
            *)
(* Output:  pairs of function call and output          \
               *)
(**********************************************************************)
newtraceParser[trace_,pattern_]:=
(*Module[{},
 Print["zzz"];
 Print[trace];
 Print[pattern];*)
 {#,ReleaseHold[#]}&/@ DeleteDuplicates[Cases[trace, HoldForm[pattern] ,{0, Infinity}]];
(* 1
]*)

traceParser[initTrace_List, parsedTrace_List, pattern_] :=    
 Module[ {print, pairs, trace},
          print =Null; (*DebugPrint[$VERBOSE, "[parser]"]*);
          print["parsedTrace = ", parsedTrace];
          trace = initTrace;
          
  pairs = Cases[trace, List[HoldForm[pattern], _], {0, Infinity}];
          If[ pairs === {},
               Return[parsedTrace]
           ];
          print["pairs = ", pairs];
       trace = 
   DeleteCases[trace //. List[HoldForm[pattern], _] :> $ZBRIC //. {$ZBRIC} -> $ZBRIC //. {$ZBRIC..} -> {$ZBRIC} //. {$ZBRIC} -> $ZBRIC, $ZBRIC, {0, Infinity}];
          print["trace = ", trace];
          traceParser[trace, Join[parsedTrace, pairs], pattern]
      ]
(*************************************************************************)
\
(* traceParse is a recursion function. In the last step either \
remaining *)
(* trace is {} or Sequence[]. First case is covered \
above,               *)
(* second case is the code below              \
                           *)
(*************************************************************************)

traceParser[parsedTrace_List, pattern_] := parsedTrace

(*


traceParser[initTrace_List, parsedTrace_List, pattern_] :=    
 Module[ {print, pairs, trace},
          print = DebugPrint[False, "[parser]"];
          print["parsedTrace = ", parsedTrace];
          trace = initTrace //. {{items___}} :> {items};
          
  pairs = Cases[trace, List[HoldForm[pattern], _], {0, Infinity}];
          If[ pairs === {},
               Return[parsedTrace]
           ];
          print["pairs = ", pairs];
          
  trace = DeleteCases[trace, 
    List[HoldForm[pattern], _], {0, Infinity}];
          print["trace = ", trace];
          traceParser[trace, Join[parsedTrace, pairs], pattern]
      ]
(*************************************************************************)
\
(* traceParse is a recursion function. In the last step either \
remaining *)
(* trace is {} or Sequence[]. First case is covered \
above,               *)
(* second case is the code below              \
                           *)
(*************************************************************************)

traceParser[parsedTrace_List, pattern_] := parsedTrace*)
    

(* ##########               main function: Test           ########### \
*)
(**********************************************************************)
(* Purpose: Test function tests all intermediate function calls using \
*)
(*          correspoinding test-functions below and prints all \
errors *)
(* Input:   any expression                                  \
          *)
(* Output:  evaluated expression or failed tests         \
             *)
(**********************************************************************)

SetAttributes[TestOperator, {HoldFirst}];
TestOperator[expression_, testFunctions_List: $TestFunctions] :=     
 Module[ {print, trace, pattern, tracePairs, traceTriples, 
   failedTests},
      	print = Print;
      	
      	print["testFunctions = ", testFunctions];
      	
      	pattern = (Alternatives[
       Sequence @@ Map[ToExpression, testFunctions]])[_][___];
      	print["pattern = ", pattern];
          
          
  trace = Trace[expression, Evaluate@pattern, TraceForward -> True];
          print["trace = ", trace];
          
          (*tracePairs = traceParser[trace, {}, pattern];*)
          
          tracePairs = newtraceParser[trace,  pattern];
       
          Print["trace pairs = ", tracePairs // TableForm];
          
          
  traceTriples = 
   tracePairs /. 
    List[HoldForm[function_[vrs_][input_]], output_] :> <|
      "function" -> function, "variables" -> vrs, 
      "input" -> input, "output" -> ReleaseHold[output]|>;
          print["trace triples = ", traceTriples // TableForm];
  
         
          
  failedTests = 
   Select[traceTriples, (ToExpression[
         "Test" ~~ 
          ToString[#function]])[#variables,#input, #output] === $Failed &];
          
          If[ failedTests === {},
               Print["Passed all tests!"];
               {True, Evaluate[expression]},
               Print["Tests below failed!"];
               {$Failed, failedTests}
           ]
      ]

(********************************************************************************)
\
(* ########## ########## ########## ########## ########## ########## \
########## *)
(********************************************************************************)






End[] (* End Private Context *)

(*EndPackage[]*)