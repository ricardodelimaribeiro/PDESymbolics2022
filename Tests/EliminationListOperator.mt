(* Wolfram Language Test file *)
	test = "Tests/EliminationListOperatorChild.mt";
		Print["   EliminationListOperator"];

   variables = Association[{
		"depVars" -> {u},
    	"indVars" -> {n,t},
    	"expression" -> u[n,t+1]+u[n,t],
    	"result" -> {{u[n,t+1],u[n,t]}}
	}];
    label = "Explicit elimination list"
    Get[ test ]
    
    variables = Association[{
		"depVars" -> {u},
    	"indVars" -> {n,t},
    	"elimOrder" -> "implicit",
    	"expression" -> u[n,t+1]+u[n,t],
    	"result" -> {{u[n,t],u[n,t+1]}}
	}];
    label = "Implicit elimination list"
    Get[ test ]