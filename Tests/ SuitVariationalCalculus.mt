(* Wolfram Language Test file *)
If[
	Length[Names["PDESymbolics2022`VarDOperator"]] == 0,
	Get[FileNameJoin[{DirectoryName[$TestFileName], "..", "PDESymbolics2022", "PDESymbolics2022.m"}]]
];
		Print["VariationalCalculus"];

TestSuite[
	{
		"VarDOperator.mt"
		,(*
		"VariationalDOperator.mt"
		,*)
		"DVarDOperator.mt"
		,
		"CleanNullLagrangiansOperator.mt"
		,
		"BasisModNullLagrangiansOperator.mt"
		,
		"RepresentModNullLagrangiansOperator.mt"
		,
		"EquivalentsByIntegrationByPartsOperator.mt"
		,
		"DisintegrateOperator.mt"
	}]
