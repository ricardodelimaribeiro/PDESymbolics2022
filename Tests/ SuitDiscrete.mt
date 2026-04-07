(* Wolfram Language Test file *)
If[
	Length[Names["PDESymbolics2022`VarDOperator"]] == 0,
	Get[FileNameJoin[{DirectoryName[$TestFileName], "..", "PDESymbolics2022", "PDESymbolics2022.m"}]]
];
		Print["Discrete"];
(*Get["/Users/ribeirrd/Library/CloudStorage/Dropbox/KAUST/PDESymbolics/\
PdeSymbolics2020/PDESymbolics2020/Discrete.m"]*)
TestSuite[
	{
		"DiscreteConservedQOperator.mt"
		,
		"TimeDifferenceOperator.mt"
		,
		"EliminationListOperator.mt"
		,
		"TimeOrderedQOperator.mt"
		,
		"FindDiscreteConservedQuantityBasisOperator.mt"
	}]
