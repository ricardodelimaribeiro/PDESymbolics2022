(* Wolfram Language Test file *)
	test = "Tests/TimeDifferenceOperatorChild.mt";
		Print["   TimeDifferenceOperator"];

   variables = Association[{
		"depVars" -> {u},
    	"indVars" -> {n,t},
    	"expression" -> u[n,t],
    	"result" -> <|"exp" -> -u[n, t] + u[n, 1 + t]|>(*u[n,t+1]-u[n,t]*)
	}];
    label = "Basic time difference"
    Get[ test ]
    
    variables = Association[{
		"depVars" -> {u},
    	"indVars" -> {n,t},
    	"timederivativeorder" -> 2,
    	"expression" -> u[n,t],
    	"result" -> <|"exp" -> u[n, t] - 2*u[n, 1 + t] + u[n, 2 + t]|>(*u[n,t+2]-2*u[n,t+1]+u[n,t]*)
	}];
    label = "Second order time difference"
    Get[ test ]
    
    variables = Association[{
		"depVars" -> {u},
    	"indVars" -> {n,t},
    	"expression" -> u[n,t],
    	"timedifference" -> (# - (# /. t -> t-1)&),
    	"result" -> <|"exp" -> u[n, t] - u[n, t-1]|>
	}];
    label = "Backward time difference"
    Get[ test ]
    
    variables = Association[{
		"depVars" -> {u},
    	"indVars" -> {n,t},
    	"expression" -> u[n,t],
    	"timedifference" -> (1/2*((# /. t -> t+1) - (# /. t -> t-1))&),
    	"result" -> <|"exp" -> 1/2*(u[n, t+1] - u[n, t-1])//Expand|>
	}];
    label = "Central time difference"
    Get[ test ]
    
    variables = Association[{
		"depVars" -> {u},
    	"indVars" -> {n,t},
    	"expression" -> u[n,t],
    	"timederivativeorder"->2,
    	"result" -> <|"exp" -> u[n, t+2] - 2*u[n, t+1] + u[n,t]|>
	}];
    label = "Second order forward time difference"
    Get[ test ]