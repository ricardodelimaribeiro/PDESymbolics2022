(* Wolfram Language Test file *)

Test[
	With[{MonList = variables["MonList"], result =variables["result"]},
		With[{ computation = BasisOperator[variables][MonList]},
    	Which[
    		result === computation,
    		True,
    		PiecewiseEqualOperator[variables][result,computation] === True,
    		True,
    		True,
    		Print["Expected output:\n",result, "Actual output\n",computation];
    		{computation, variables}
    	]
	]
	]
    ,
    True
    ,
    TestID -> "BasisOperator-20201202-M7B7R1_" <> label
]
