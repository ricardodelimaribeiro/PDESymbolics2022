(* Wolfram Language Test file *)

Test[
	With[{expression = variables["expression"]},
		result = FullSimplify[VariationalDOperator[variables][expression]]; (*ConstantArray[0,Length[variables["depVars"]]];*)
		FullSimplify[VarDOperator[variables][expression]]
	]
    ,
    result
    ,
    TestID -> "VarDOperator-20200420-F627R8_" <> label
]
