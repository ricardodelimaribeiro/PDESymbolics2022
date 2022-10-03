(* Wolfram Language Test file *)

Test[
	With[{sol = GenericLinearCombinationOperator[options][list]},
		If[sol =!= options["result"],
			Print["Used UniqueConstantCleaner in test whose label is\n\"" <> label <>"\""];
			UniqueConstantsCleaner[Lookup[options,"coeff",\[FormalA]]][sol],
			sol
		]
	]
    ,
    options["result"]
    ,
    TestID -> "GenericLinearCombinationOperator-20210128-F6M5R8_" <> label
]
