(* Wolfram Language Test file *)
If[
	Length[Names["PDESymbolics2022`VarDOperator"]] == 0,
	Get[FileNameJoin[{DirectoryName[$TestFileName], "..", "PDESymbolics2022", "PDESymbolics2022.m"}]]
];
		Print["Parametric Groebner Basis"];
TestSuite[
	{
		"AutoReduceOperator.mt"
		,
		"InferGeneratorsOperator.mt"
		,
		"LeadingCoefficientOperator.mt"
		,
		"LeadingTermOperator.mt"
		,
		"GrobOp.mt"
	}]
