(* Wolfram Language Test file *)
	test = "Tests/TimeOrderedQOperatorChild.mt";
		Print["   TimeOrderedQOperator"];

   variables = Association[{
		"depVars" -> {u},
    	"indVars" -> {n,t},
    	"expression" -> Sequence[u[n,t+1],u[n,t]],
    	"result" -> True
	}];
    label = "Explicit time ordering 1"
    Get[ test ]
    
    variables = Association[{
		"depVars" -> {u,v},
    	"indVars" -> {n,t},
    	"expression" -> Sequence[u[n+2,t+1],v[n+3,t]],
    	"result" -> True
	}];
    label = "Explicit time ordering 2"
    Get[ test ]
    
    variables = Association[{
		"depVars" -> {u,v},
    	"indVars" -> {n,t},
    	"expression" -> Sequence[u[n+2,t-1],v[n+3,t+2]],
    	"result" -> False
	}];
    label = "Explicit time ordering 3"
    Get[ test ]
    
    variables = Association[{
		"depVars" -> {u},
    	"indVars" -> {n,t},
    	"elimOrder" -> "implicit",
    	"expression" -> Sequence[u[n,t+1],u[n,t]],
    	"result" -> False
	}];
    label = "Implicit time ordering 1"
    Get[ test ]
    
    variables = Association[{
		"depVars" -> {u},
    	"indVars" -> {n,t},
    	"elimOrder" -> "implicit",
    	"expression" -> Sequence[u[n+2,t+1],u[n+2,t+1]],
    	"result" -> True
	}];
    label = "Implicit time ordering 2"
    Get[ test ]
    
    variables = Association[{
		"depVars" -> {u,v},
    	"indVars" -> {n,t},
    	"elimOrder" -> "implicit",
    	"expression" -> Sequence[u[n+2,t+1],v[n+2,t+1]],
    	"result" -> True
	}];
    label = "Implicit time ordering 3"
    Get[ test ]
    
    variables = Association[{
		"depVars" -> {u,v},
    	"indVars" -> {n,t},
    	"elimOrder" -> "implicit",
    	"expression" -> Sequence[u[n+2,t+1],v[n+2,t]],
    	"result" -> False
	}];
    label = "Implicit time ordering 4"
    Get[ test ]