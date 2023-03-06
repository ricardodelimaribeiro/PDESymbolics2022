(* Wolfram Language package *)
General::KeyAbsent = "Key `1` is missing. Proceeding with `2`.";
Clear[keyAbsentMessage];
keyAbsentMessage::usage = 
"keyAbsentMessage[OperatorName][Key(s)][Standard Ouput] will print a the General::KeyAbsent message";
keyAbsentMessage[op_][vars_][std_] := (Message[op::KeyAbsent, vars, std]; std) 
