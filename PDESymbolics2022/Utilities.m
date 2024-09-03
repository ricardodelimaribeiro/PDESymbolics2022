(* Wolfram Language Package *)
(*BeginPackage["PDESymbolics2020`Utilities`"]*)
MKF::usage = 
"MKF is a function of two variables [argument, value] that works like
Function[Evaluate[argument], Evaluate[value]]";

getVars::usage =
"getVars[expr, depVars, opt, level] internal function that gets all variables such as derivatives of dependent variables from an expression";

GetVarsOperator::usage = 
"GetVarsOperator[variables][xp] operator version of getVars"

FreeQQ::usage =
"FreeQQ[expr, form] returns FreeQ[expr, form] or And@@Map[FreeQ[expr, #]&, forms] if forms is a list."

zeroq::usage =
"zeroq[xp] returns xp == 0 or a conjuntion of such equations if xp is a list."

Begin["`Private`"] (* Begin Private Context *) 
zeroq[xp_List] :=
    And @@ zeroq /@ xp;

zeroq[xp_] :=
    (xp // Expand // Simplify) == 0

MKF = Function[#1, #2] &;

getVars[expr_, depVars_List, opt_:Default, level_:{0,Infinity}] :=
    With[ {vars = Union@Cases[expr, (Alternatives @@ depVars)[___] | Derivative[__][Alternatives @@ depVars][___], level]},
        If[ opt === Full,(* when should this give more terms than vars?*)
            Join[Select[depVars, !FreeQ[expr, #] && FreeQ[vars, #]&], vars],
            vars
        ]
    ];
    
getVarsOperator[variables_][expr_] :=
    getVars[expr, Lookup[variables,"depVars",{}]]

GetVarsOperator = Kleisli[getVarsOperator]

FreeQQ[expr_, form_] :=
    FreeQ[expr, form];

FreeQQ[expr_, forms_List] :=
    And@@Map[FreeQ[expr, #]&, forms];
    
(* ##########         cosmetic-function: DebugPrint       ########### *)
(**********************************************************************)
(* Usage:   DebugPrint[flag, initMessage]                             *)
(* Purpose: Produces printing functions for debugging for other       *)
(*          functions. Flag can be any name related to a function     *)
(*          to be debbuged.                                           *)
(* Input:   flag, e.g. $NameOfTheFunction                             *)
(* Output:  Print function for debugging                              *)
(**********************************************************************)
DebugPrint[flag_, initMessage_:""] :=
    If[ flag,
        Print[initMessage, ##]
    ]&;    

End[] (* End Private Context *)
(*EndPackage[]*)