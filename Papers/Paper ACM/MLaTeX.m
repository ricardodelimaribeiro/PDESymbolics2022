(* ::Package:: *)

BeginPackage["MLaTeX`"]
Needs["CellsToTeX`"]


MLaTeX::usage="Processes the file"

(* Basic LaTeX check *)

LATEXSANITYCHECK::usage="Minimal check on latex";
BASICLATEXVALIDATION::usage="Checks if all environments open and closes, checks if
braces are balanced in text and if all formulas open and close";

(* clean up and includes handling *)

BASICTEXTCLEAN::usage="Takes a LaTeX string and returns the file without comments both % and {comment} environment. Also replaces \\n\\r by \\n. ";
BASICTEXTCLEANA::usage="just like BASICTEXTCLEAN but does not clean mmacells and algorithms";
BASICINCLUDE::usage="Scans string for \\input and replaces the appropriate file";
BASICINCLUDEREMOVER::usage="Scans string for \\input and if the file does not exist removes \\input";
BEGINENDDOCCLEANER::usage="Replaces macros for begin{document} and end{document}";
INCLUDEANDCLEAN::usage="Applies BASICTEXTCLEAN followed by BASICINCLUDE until a fixed point is reached";
INCLUDEANDCLEANA::usage="Applies BASICTEXTCLEANA followed by BASICINCLUDE until a fixed point is reached";
MLaTeXMARKUPREMOVER::usage="Takes a string, removes MLATEX PATTERNS, replaces mequation by equation, removes MLaTex Package";
FORMULAFIXER::usage="Replaces in a string $$...$$ by \\[...\\] and $...$ by \\(...\\)";

(* TO BE REMOVED IF REPLACED BY NEW METHODS*)

LATEXFORMULACLEANER::usage="Removes formulas and images and replaces formulas by [1]"; 
LATEXONLYFORMULACLEANER::usage="Removes formulas them by [1]"; 
PUNCTUATIONCLEANER::usage="Moves punctuation outside formulas";

(* readibility *)

ARI::usage="Automatic readibility index"

(* Coleman-Liau index - estimated *)

CLI::usage="Coleman-Liau index";

(* Smog index - estimated *)

SMOG::usage="Smog index"

(* Glue index *)

Glue::usage="Glue index";


TextStatisticalInformation::usage="Returns an association with basic text statistical information";

(****************)

DEEPCLEAN::usage="DEEPCLEAN[Text, bool] if bool=False returns text, otherwise returns a agressively cleaned version of Text";


(* Auxiliary functions *)


balancedBracesQ::usage="Takes a string and checks if the braces { } are balanced";
MatchingEnvQ::usage="Takes a string and checks if all begin{env} closes with end{env}";

(* Feature extraction functions *)

PREAMBLEANDDOC::usage="Splits a string into the preamble and document - ignores all after \\end{document}";
NCOMEXTRACT::usage="Extracts the newcommand environments";
NCOMMTORULES::usage="Transform newcommand environments into replacement rules";
SORTNCOMMTORULES::usage="Sorts rules";
Extractor::usage="Extracts text between delimiters and removes delimiters";
Extractor2::usage="Extracts text between delimiters";

(* TABLE CREATION *)

MAKETABLE::usage="Runs the code TBL and generates a LaTeX tabular environment; TBLOPEN, TBLSEP and TBLCLOSE can be customized";

(* TEXT ANALYSIS *)

BasicTextStatistics::usage="Returns basic text statistics";
BasicTextStatisticsTex::usage="Returns basic text statistics in LaTeX form";
GenAnnLaTeX::usage="Generates annotated LaTeX";
ProcessText::usage="Pre-processes the text to generate annotated latex";

(* EQUATION VALIDATION *)

EquationValidation::usage="Takes a latex equation and returns a string with possible errors";


FORMULAVARIABLES::usage="Extracts variables from formulas";
FORMULASCHECKRULES::usage="Rules to check formulas for typos";
FORMULASPATTERNS::usage="Patterns for formulas in latex";

$BASEDIR::usage="File base directory";



Begin["`Private`"]


(*******************************)
(*  PATTERNS AND RULES        *)
(*******************************)

MLATEXPATTERNS:={Shortest["\\begin{ASP}"~~__~~"\\end{ASP}" ], Shortest["\\begin{CLM}"~~__~~"\\end{CLM}" ],
Shortest["\\begin{LMA}"~~__~~"\\end{LMA}" ], Shortest["\\begin{THM}"~~__~~"\\end{THM}" ],
Shortest["\\begin{DEF}"~~__~~"\\end{DEF}" ], 
Shortest["\\begin{ART}"~~__~~"\\end{ART}" ], Shortest["\\begin{IMG}"~~__~~"\\end{IMG}" ],
Shortest["\\begin{FRM}"~~__~~"\\end{FRM}" ],
Shortest["\\begin{FRM*}"~~__~~"\\end{FRM*}"], 
Shortest["\\begin{FRMI}"~~__~~"\\end{FRMI}"], 
Shortest["\\begin{PRE}"~~__~~"\\end{PRE}"],Shortest["\\begin{MOV}"~~__~~"\\end{MOV}"], 
Shortest["\\begin{TBL}"~~__~~"\\end{TBL}" ], 
Shortest["\\begin{LST}"~~__~~"\\end{LST}" ],
Shortest["\\begin{EXE}"~~__~~"\\end{EXE}" ],
Shortest["\\begin{PEX}"~~__~~"\\end{PEX}" ] };

MLATEXPATTERNSREMOVERULES:=Map[#->""&,MLATEXPATTERNS];

FORMULASPATTERNS:={Shortest["\\begin{mmaCell}"~~__~~"\\end{mmaCell}"], Shortest["\\begin{algorithm}"~~__~~"\\end{algorithm}"],
Shortest["\\begin{gather}"~~__~~"\\end{gather}"],Shortest["\\begin{gather*}"~~__~~"\\end{gather*}"],
Shortest["\\["~~__~~"\\]" ],Shortest["\\("~~__~~"\\)" ],Shortest["\\begin{equation}"~~__~~"\\end{equation}" ],Shortest["\\begin{equation*}"~~__~~"\\end{equation*}" ],Shortest["\\begin{mathequation}"~~__~~"\\end{mathequation}" ],Shortest["\\begin{mathequation*}"~~__~~"\\end{mathequation*}" ],
 Shortest["\("~~__~~"\)" ],Shortest["\\begin{align}"~~__~~"\\end{align}" ],Shortest["\\begin{flalign}"~~__~~"\\end{flalign}" ],Shortest["\\begin{flalign*}"~~__~~"\\end{flalign*}" ],
Shortest["\\begin{align*}"~~__~~"\\end{align*}" ],Shortest["\\begin{eqnarray}"~~__~~"\\end{eqnarray}" ],Shortest["\\begin{displaymath}"~~__~~"\\end{displaymath}" ],Shortest["\\begin{eqnarray*}"~~__~~"\\end{eqnarray*}" ],Shortest["\\begin{multline}"~~__~~"\\end{multline}" ],Shortest["\\begin{multline*}"~~__~~"\\end{multline*}" ]};

LATEXOTHERREMOVERULES:=StringReplace[StringReplace[#, Shortest["\\hbox{"~~(arg1__/;balancedBracesQ[arg1])~~"}"]->""],{Shortest["\\begingroup"~~__~~"\\endgroup" ]->"[1]","\\usepackage{subcaption}"->"", "\\usepackage{showkeys}"->"", "\\usepackage{refcheck}"->"",Shortest["\\begin{figure}"~~__~~"\\end{figure}" ]->"",
Shortest["\\begin{verbatim}"~~__~~"\\end{verbatim}" ]->"",Shortest["\\pause" ]->"",  "\\eqref{}"->"[1]", "\\ref{}"->"[1]", "\\cite{}"->"[1]",Shortest["\\cite{"~~(arg1__/;balancedBracesQ[arg1])~~"}" ]->"[1]",Shortest["\\ref{"~~__~~"}" ]->"[1]",Shortest["\\eqref{"~~__~~"}" ]->"[1]","\\begin{proof}"->"", "\\end{proof}"->"" ,Shortest["\\begin{tabular}"~~__~~"\\end{tabular}" ]->"[1]","\\sc "->"","\\it "->"","\\bf "->""}]&;

OTHERPATTERNS:={Shortest["\\begin{verbatim}"~~__~~"\\end{verbatim}" ]};


(**********************)
(* CLEANUP FUNCTIONS *)
(**********************)

PRIMARYTEXTCLEANA:=StringReplace[StringReplace[StringReplace[StringReplace[StringReplace[#,{"\r\n"->"\n", "\\\\%"->"\\\\ %", "\\\\{"->"\\\\ {", "\\\\}"->"\\\\ }", "\\\\$"->"\\\\ $"}], "\r"->"\n"], Shortest["\n"~~(" "|"\t")..~~"%"]->"\n%"],(x_/;NE2[x])~~Shortest[("%"~~___~~"\n")]:>If[x=="\n", "\n",x~~"\n"]],{Shortest["\\begin{comment}"~~__~~"\\end{comment}"]->""}]&;

PRIMARYTEXTCLEAN:=StringReplace[StringReplace[StringReplace[StringReplace[StringReplace[#,{"\r\n"->"\n", "\\\\%"->"\\\\ %", "\\\\{"->"\\\\ {", "\\\\}"->"\\\\ }", "\\\\$"->"\\\\ $"}], "\r"->"\n"], Shortest["\n"~~(" "|"\t")..~~"%"]->"\n%"],(x_/;NE2[x])~~Shortest[("%"~~___~~"\n")]:>If[x=="\n", "\n",x~~"\n"]],{Shortest["\\begin{mmaCell}"~~__~~"\\end{mmaCell}"]->"", Shortest["\\begin{algorithm}"~~__~~"\\end{algorithm}"]->"",Shortest["\\begin{comment}"~~__~~"\\end{comment}"]->""}]&;

BASICTEXTCLEAN[txt_]:=If[StringMatchQ[#, ___~~"%"~~Whitespace...], StringReplace[#, "%"~~Whitespace...->""], #]&@FixedPoint[PRIMARYTEXTCLEAN, txt];

BASICTEXTCLEANA[txt_]:=If[StringMatchQ[#, ___~~"%"~~Whitespace...], StringReplace[#, "%"~~Whitespace...->""], #]&@FixedPoint[PRIMARYTEXTCLEANA, txt];


(* replaces \input by existing files *)


Renamer=If[FileExistsQ[#], #, #<>".tex"]&;


BASICINCLUDE[txt_]:=StringReplace[StringReplace[txt, "\\include{"->"\\vfill\\pagebreak\\input{"], Map[#->BASICTEXTCLEAN@Import[Renamer@StringReplace[#, {"\\input{"->"", "}"->""}], "Text"]&, Select[StringCases[txt,Shortest["\\input{"~~__~~"}"]],Function[xxx,FileExistsQ@Renamer@StringReplace[xxx,{"\\input{"->"","}"->""}]]]]];
(* removes \input of non-existing files *)

BASICINCLUDEREMOVER[txt_]:=StringReplace[txt, Map[#->""&, Select[StringCases[txt,Shortest["\\input{"~~__~~"}"]],Function[xxx,!FileExistsQ@StringReplace[xxx,{"\\input{"->"","}"->""}]]]]];

(* searches for macros for begin document and end document - replaces them and cleans *)

BEGINENDDOCCLEANER[TXTOR_]:=Module[{RAWCOM, BDOC, EDOC, OUT, BDOC2, EDOC2, EDOC3, BDOC3},RAWCOM:=StringTake[#, Min[240, StringLength[#]]]&/@(Rest@StringSplit[TXTOR, "\\newcommand"|"\\def"|"\\renewcommand"]);
BDOC=Select[RAWCOM,StringMatchQ[#, "{"~~(x__/;balancedBracesQ[x])~~"}{\\begin{document}"~~___]&];
EDOC=Select[RAWCOM,StringMatchQ[#, "{"~~(x__/;balancedBracesQ[x])~~"}{\\end{document}"~~___]&];
OUT=TXTOR;
If[Length@BDOC>0, 
BDOC2:=Map[StringCases[#,  "{"~~(x__/;balancedBracesQ[x])~~"}{\\begin{document}"~~___->"{"~~x~~"}{\\begin{document}}"][[1]]&, EDOC];
BDOC3:=StringCases[Last@EDOC2,  "{"~~(x__/;balancedBracesQ[x])~~"}{\\begin{document}"->x][[1]];
OUT=StringReplace[StringReplace[TXTOR, Map[#->"{\\hgsajdhgjdasgjadhg}{}"&, BDOC2]],EDOC3~~(x_/;Not[LetterQ[x]])->"\\begin{document}"~~x];
];
If[Length@EDOC>0, 
EDOC2:=Map[StringCases[#,  "{"~~(x__/;balancedBracesQ[x])~~"}{\\end{document}"~~___->"{"~~x~~"}{\\end{document}}"][[1]]&, EDOC];
EDOC3:=StringCases[Last@EDOC2,  "{"~~(x__/;balancedBracesQ[x])~~"}{\\end{document}"->x][[1]];
OUT=StringReplace[StringReplace[OUT, Map[#->"{\\hgsajdhgjdasgjadhg}{}"&, EDOC2]], EDOC3~~(x_/;Not[LetterQ[x]])->"\\end{document}"~~x];
];
OUT
];


INCLUDEANDCLEAN:=Function[TXT,BEGINENDDOCCLEANER@FixedPoint[BASICINCLUDE[BASICTEXTCLEAN[#]]&, TXT]];
INCLUDEANDCLEANA:=Function[TXT,BEGINENDDOCCLEANER@FixedPoint[BASICINCLUDE[BASICTEXTCLEANA[#]]&, TXT]];

(* uses MLATEX PATTERS to remove, replace mequation by equation, removes MLaTex Package *)

MLaTeXMARKUPREMOVER:=StringReplace[#,Join[MLATEXPATTERNSREMOVERULES, {"\\usepackage{MLaTeX}"->"","\\usepackage[invisible]{MLaTeX}"->"", "\\usepackage{M-LaTeX}"->"","\\usepackage[invisible]{M-LaTeX}"->"", "{mathequation}"->"{equation}", "{mathequation*}"->"{equation*}"}]]&;


FORMULAFIXER[txt_?StringQ]:=StringReplace[StringReplace[StringReplace[StringReplace[txt,{"\\\\$"->"\\\\ $", "\\\\("->"\\\\ (", "\\\\)"->"\\\\ )", "\\\\["->"\\\\ [", "\\\\]"->"\\\\ ]" }],  {Shortest["\\hbox{"~~(z__/;balancedBracesQ[z])~~"}"]->("\\hbox{"~~FORMULAFIXER[z]~~"}"),Shortest["\\mbox{"~~(z__/;balancedBracesQ[z])~~"}"]->("\\mbox{"~~FORMULAFIXER[z]~~"}")}],Shortest["$$"~~ww:__~~"$$"]->"\\["~~ww~~"\\]"],Shortest[(x_/;NE[x])~~"$"~~w:___~~(z_/;NE[z])~~"$"]->(x~~"\\("~~w~~z~~"\\)")];  


PUNCTUATIONCLEANER:=Module[{TT2,TT3,TT4, RulesTT},
TT2=FORMULAFIXER[#];
TT3=StringCases[TT2, 
Shortest[("\\["|"\\("|"\\begin{gather}"|"\\begin{gather*}"|"\\begin{equation}"|"\\begin{equation*}"|"\\begin{flalign*}"|"\\begin{flalign}"|"\\begin{align}"|"\\begin{align*}"|"\\begin{multline}"|"\\begin{multline*}"|"\\begin{eqnarray}"|"\\begin{eqnarray*}"|"\\begin{mathequation}"|"\\begin{mathequation*}")~~x:__~~
("\\]"|"\\)"|"\\end{gather}"|"\\end{gather*}"|"\\end{equation}"|"\\end{equation*}"|"\\end{flalign}"|"\\end{flalign*}"|"\\end{align}"|"\\end{align*}"|"\\end{multline}"|"\\end{multline*}"|"\\end{eqnarray}"|"\\end{eqnarray*}"|"\\end{mathequation}"|"\\end{mathequation*}")]];
TT4=Map[StringReplace[#,{Shortest[(x:"."|","|";")~~(Whitespace|"\n"|"\r\n"|""|"\\end{aligned}"|"\\end{cases}"|"\\end{split}")..~~(z:"\\]"|"\\)"|"\\end{gather}"|"\\end{gather*}"|"\\end{equation}"|"\\end{equation*}"|"\\end{flalign*}"|"\\end{flalign}"|"\\end{align}"|"\\end{align*}"|"\\end{multline}"|"\\end{multline*}"|"\\end{eqnarray}"|"\\end{eqnarray*}"|"\\end{mathequation}"|"\\end{mathequation*}")]->z~~x }]& , TT3];
RulesTT= MapThread[#1->#2&, {TT3, TT4}];
StringReplace[TT2,RulesTT]
]&;


BIBCLEAN=StringReplace[#, Shortest["\\begin{thebibliography}"~~__~~"\\end{thebibliography}"]->""]&;

(* WE ARE MISSING A VERBATIM CLEANER AND A GENERAL PURPOSE COMMAND CLEANER.
IN ADDITION, WE NEED A SECTION/CHAPTER FIXER *)


DEEPCLEAN=
If[!#2,
#1,
Module[{TAA, TAAA, TA, TB},

(*remove verbatim - this is necessary otherwise the LaTeX can get completely messed up *)

TAA=StringReplace[RemoveDiacritics@#1,{
Shortest["\\begin{verbatim}"~~__~~"\\end{verbatim}" ]->"",
Shortest["\\verb"~~(x_~~___~~x_/;Not[LetterQ[x]])]->""}]; 

(* fixing the sections so that punctuation does not get messed up *)
 
TAAA=StringReplace[TAA, 
{Shortest["\\section{"~~(arg1__/;balancedBracesQ[arg1])~~"}"]->(arg1~~".\n\n"), 
Shortest["\\subsection{"~~(arg1__/;balancedBracesQ[arg1])~~"}"]->arg1~~".\n\n",
Shortest[ "\\subsubsection{"~~(arg1__/;balancedBracesQ[arg1])~~"}"]->arg1~~".\n\n", 
Shortest["\\chapter{"~~(arg1__/;balancedBracesQ[arg1])~~"}"]->arg1~~".\n\n",
Shortest["\\section*{"~~(arg1__/;balancedBracesQ[arg1])~~"}"]->(arg1~~".\n\n"), 
Shortest["\\subsection*{"~~(arg1__/;balancedBracesQ[arg1])~~"}"]->arg1~~".\n\n",
Shortest[ "\\subsubsection*{"~~(arg1__/;balancedBracesQ[arg1])~~"}"]->arg1~~".\n\n", 
Shortest["\\chapter*{"~~(arg1__/;balancedBracesQ[arg1])~~"}"]->arg1~~".\n\n"}]; 


(* cleans the bibliography and removes the remaining \begin{} \end{} *)

TA=StringReplace[BIBCLEAN@TAAA,{Shortest["\\begin{"~~(arg1__/;balancedBracesQ[arg1])~~"}"]->"", Shortest["\\end{"~~(arg1__/;balancedBracesQ[arg1])~~"}"]->"", Shortest["\\label{"~~(arg1__/;balancedBracesQ[arg1])~~"}"]->""}];

(* cleans some random stuff that was causing issues *)

TB=StringReplace[TA, {
Shortest["\\label{"~~(x__/;balancedBracesQ[x])~~"}"]->"",
Shortest["\\thlabel{"~~(x__/;balancedBracesQ[x])~~"}"]->"",
"\\inputpdf"->"",
Shortest["\\arraycolsep{"~~(x__/;balancedBracesQ[x])~~"}"]->"", 
"\\bibinfo"->"",
 "\\bibnamefont"->"", 
"\\autbiinnerbib"->"",
"\\citenamefont"->"", 
"\\Eprint"->"",
((x_/;NE[x])~~("@"|"#"))->"",
"\\;"->"","\\$"->"", "\\!"->"",
"\\renewcommand"->"", "\\newcommand"->"",
"#"->"", Shortest["\\color{"~~(x__/;balancedBracesQ[x])~~"}"]->" ",
 Shortest["\\teaser{"~~(x__/;balancedBracesQ[x])~~"}"]->" ", 
"\\usepackage{graphicx}"->"","\\usepackage{caption}"->"",
 "\\usepackage{subcaption}"->"", "\\pagebreak"->"", "\\inputgraphics"->""}];

(* finally removes remaining commands *)

StringReplace[TB, Shortest["\\"~~__~~(x_/;Not[LetterQ[x]])]->x] 
]
]&;








MBOXCLEANER[txt_?StringQ]:=StringReplace[txt, {Shortest["\\mbox{"~~__~~"}"]->" ", Shortest["\\hbox{"~~__~~"}"]->" "}]; (* THIS IS A TEMPORARY FIX FOR MBOX *)


LATEXFORMULACLEANER=StringReplace[StringReplace[MBOXCLEANER[#], Shortest["\\hbox{"~~(arg1__/;balancedBracesQ[arg1])~~"}"]->""],{
Shortest["\\begingroup"~~__~~"\\endgroup" ]->"[1]","\\usepackage{subcaption}"->"", "\\usepackage{showkeys}"->"", 
"\\usepackage{refcheck}"->"",Shortest["\\["~~__~~"\\]" ]->"[1]", Shortest["\\("~~__~~"\\)" ]->"[1]",
Shortest["\\pause" ]->"", Shortest["\\begin{equation}"~~__~~"\\end{equation}" ]->"[1]",
Shortest["\\begin{equation*}"~~__~~"\\end{equation*}" ]->"[1]",Shortest["\\begin{mathequation}"~~__~~"\\end{mathequation}" ]->"[1]",
Shortest["\\begin{mathequation*}"~~__~~"\\end{mathequation*}" ]->"[1]",
Shortest["$$"~~__~~"$$" ]->"[1]",Shortest["$"~~__~~"$" ]->"[1]", Shortest["\("~~__~~"\)" ]->"[1]",
 "\\eqref{}"->"[1]", "\\ref{}"->"[1]", "\\cite{}"->"[1]",
Shortest["\\cite{"~~(arg1__/;balancedBracesQ[arg1])~~"}" ]->"[1]",
Shortest["\\citep{"~~(arg1__/;balancedBracesQ[arg1])~~"}" ]->"[1]", "\\shortcite{}"->"[1]",
Shortest["\\shortcite{"~~(arg1__/;balancedBracesQ[arg1])~~"}" ]->"[1]", 
Shortest["\\ref{"~~__~~"}" ]->"[1]",Shortest["\\eqref{"~~__~~"}" ]->"[1]",
Shortest["\\thref{"~~__~~"}" ]->"[1]",
Shortest["\\begin{flalign}"~~__~~"\\end{flalign}" ]->"[1]",
Shortest["\\begin{flalign*}"~~__~~"\\end{flalign*}" ]->"[1]",
Shortest["\\begin{align}"~~__~~"\\end{align}" ]->"[1]", Shortest["\\begin{figure}"~~__~~"\\end{figure}" ]->"",
Shortest["\\begin{figure*}"~~__~~"\\end{figure*}" ]->"",
Shortest["\\begin{align*}"~~__~~"\\end{align*}" ]->"[1]", "\\begin{proof}"->"", "\\end{proof}"->"",
Shortest["\\begin{eqnarray}"~~__~~"\\end{eqnarray}" ]->"[1]",Shortest["\\begin{displaymath}"~~__~~"\\end{displaymath}" ]->"[1]",
Shortest["\\begin{eqnarray*}"~~__~~"\\end{eqnarray*}" ]->"[1]" , Shortest["\\begin{multline}"~~__~~"\\end{multline}" ]->"[1]",
Shortest["\\begin{multline*}"~~__~~"\\end{multline*}" ]->"[1]", Shortest["\\begin{tabular}"~~__~~"\\end{tabular}" ]->"[1]",
Shortest["\\begin{mmaCell}"~~__~~"\\end{mmaCell}"]->"", Shortest["\\begin{algorithm}"~~__~~"\\end{algorithm}"]->"",
Shortest["\\begin{gather}"~~__~~"\\end{gather}"]->"[1]",Shortest["\\begin{gather*}"~~__~~"\\end{gather*}"]->"[1]",
"\\sc "->"","\\it "->"","\\bf "->""}]&;

LATEXONLYFORMULACLEANER=StringReplace[StringReplace[MBOXCLEANER[#], Shortest["\\hbox{"~~(arg1__/;balancedBracesQ[arg1])~~"}"]->""],{
Shortest["\\begingroup"~~__~~"\\endgroup" ]->"[1]","\\usepackage{subcaption}"->"", "\\usepackage{showkeys}"->"", "\\usepackage{refcheck}"->"",Shortest["\\["~~__~~"\\]" ]->"[1]", Shortest["\\("~~__~~"\\)" ]->"[1]",Shortest["\\pause" ]->"", Shortest["\\begin{equation}"~~__~~"\\end{equation}" ]->"[1]",Shortest["\\begin{equation*}"~~__~~"\\end{equation*}" ]->"[1]",Shortest["\\begin{mathequation}"~~__~~"\\end{mathequation}" ]->"[1]",Shortest["\\begin{mathequation*}"~~__~~"\\end{mathequation*}" ]->"[1]",
Shortest["$$"~~__~~"$$" ]->"[1]",Shortest["$"~~__~~"$" ]->"[1]", Shortest["\("~~__~~"\)" ]->"[1]", "\\eqref{}"->"[1]", "\\ref{}"->"[1]", "\\cite{}"->"[1]",
Shortest["\\cite{"~~(arg1__/;balancedBracesQ[arg1])~~"}" ]->"[1]",Shortest["\\citep{"~~(arg1__/;balancedBracesQ[arg1])~~"}" ]->"[1]", "\\shortcite{}"->"[1]",
Shortest["\\shortcite{"~~(arg1__/;balancedBracesQ[arg1])~~"}" ]->"[1]", Shortest["\\ref{"~~__~~"}" ]->"[1]",Shortest["\\eqref{"~~__~~"}" ]->"[1]",
Shortest["\\thref{"~~__~~"}" ]->"[1]",
Shortest["\\begin{align}"~~__~~"\\end{align}" ]->"[1]",
Shortest["\\begin{align*}"~~__~~"\\end{align*}" ]->"[1]", "\\begin{proof}"->"", "\\end{proof}"->"", 
Shortest["\\begin{eqnarray}"~~__~~"\\end{eqnarray}" ]->"[1]",Shortest["\\begin{displaymath}"~~__~~"\\end{displaymath}" ]->"[1]",
Shortest["\\begin{eqnarray*}"~~__~~"\\end{eqnarray*}" ]->"[1]" , Shortest["\\begin{multline}"~~__~~"\\end{multline}" ]->"[1]",
Shortest["\\begin{multline*}"~~__~~"\\end{multline*}" ]->"[1]", Shortest["\\begin{tabular}"~~__~~"\\end{tabular}" ]->"[1]",
Shortest["\\begin{mmaCell}"~~__~~"\\end{mmaCell}"]->"", Shortest["\\begin{algorithm}"~~__~~"\\end{algorithm}"]->"",
Shortest["\\begin{gather}"~~__~~"\\end{gather}"]->"[1]",Shortest["\\begin{gather*}"~~__~~"\\end{gather*}"]->"[1]",
"\\sc "->"","\\it "->"","\\bf "->""}]&;





(**********************)
(* AUXILIARY FUNCTIONS *)
(**********************)

NE[x_?StringQ]:=!(x=="\\");
NE2[x_?StringQ]:=!(x=="\\"||x=="%");
NE3[x_?StringQ]:=!(x=="\\"||x=="%"||x==" "||x=="\t");
NN[x_?StringQ]:=!StringContainsQ[x,"\n"];


balancedBracesQ[str_String]:=((StringCount[str,"{"]-StringCount[str,"\\{"]-StringCount[str,"}"]+StringCount[str,"\\}"])===0);

(***********************************************)
(* FEATURE EXTRACTION FUNCTIONS*)
(*                                            *)
(***********************************************)


(* THIS IS A QUICK FIX TO EXTRACT NEWCOMMANDS - we are not extracting yet thinks like
\newcommand\ar {sagdfga} or \def\x\quad etc but if this works this should not be so hard *)

DefFixer=StringReplace[#, Shortest[z:("\\def"|"\\newcommand"|"\\renewcommand")~~Whitespace...~~"\\"~~(x__/;LetterQ[x])~~Whitespace...~~"{"~~(y__/;balancedBracesQ[y])~~"}"]:>z~~"{\\"~~x~~"}{"~~y~~"}"]&;

(*NCOMEXTRACT:=
Function[TXTOR, Module[{RAWCOM}, 
RAWCOM=StringTake[#, Min[240, StringLength[#]]]&/@Rest@StringSplit[DefFixer@TXTOR, "\\newcommand"|"\\def"|"\\renewcommand"];
"\\newcommand{"~~#[[1]]~~"}{"~~#[[2]]~~"}"&/@Flatten[Map[StringCases[#,"{"~~(x__/;balancedBracesQ[x])~~"}{"~~(y__/;balancedBracesQ[y])~~"}"~~___->{x,y}]&, Select[RAWCOM, StringMatchQ[#, "{"~~(x__/;balancedBracesQ[x])~~"}{"~~(y__/;balancedBracesQ[y])~~"}"~~___]&]],1]
]];*)

NCOMEXTRACT:=
Function[TXTOR, Module[{RAWCOM}, 
RAWCOM=StringTake[#, Min[240, StringLength[#]]]&/@Rest@StringSplit[DefFixer@TXTOR, "\\newcommand"|"\\def"|"\\renewcommand"];
"\\newcommand{"~~#[[1]]~~"}{"~~#[[2]]~~"}"&/@Flatten[StringCases[#,Shortest["{"~~(x__/;balancedBracesQ[x])~~"}{"~~(y__/;balancedBracesQ[y])~~"}"]~~___:>{x,y}]&/@ Select[RAWCOM, StringMatchQ[#, "{"~~(x__/;balancedBracesQ[x])~~"}{"~~(y__/;balancedBracesQ[y])~~"}"~~___]&],1]
]];


NCOMMTORULES:=Function[NCOMM,
MapThread[#1->#2&,{StringReplace[NCOMM,Shortest[("\\newcommand{"|"\\renewcommand{")~~(arg1__/;balancedBracesQ[arg1])~~"}{"~~(arg2__/;balancedBracesQ[arg2])~~"}"]->(arg1~~(x_/;Not[LetterQ[x]]))], StringReplace[NCOMM,Shortest[("\\newcommand{"|"\\renewcommand{")~~(arg1__/;balancedBracesQ[arg1])~~"}{"~~(arg2__/;balancedBracesQ[arg2])~~"}"]->(arg2~~x)]}]];

SORTNCOMMTORULES:=Function[R, Sort[R, Length[Key[#1]]> Length[Key[#2]]&]];


PREAMBLEANDDOC:=StringSplit[#,{"\\begin{document}", "\\end{document}"}][[1;;2]]&;

Remover[txt_,Delim_]:=StringReplace[txt,Map[#->""&,Flatten[Delim]]];

Extractor[txt_,Delim_]:=Remover[StringCases[txt,Map[Shortest[#[[1]]~~__~~#[[2]]]&, Delim]], Delim];
Extractor2[txt_,Delim_]:=StringCases[txt,Map[Shortest[#[[1]]~~__~~#[[2]]]&, Delim]];



(*******************************************************************************)
(* TABLE CREATION FUNCTIONS                                                  *)
(******************************************************************************)

MAKETABLE[TBL_]:=Module[{TBLPROCESSED, TBLOPEN, TBLCLOSE, TBLSEP},
TBLPROCESSED=ToExpression[TBL];
PRINT["*******"];
Print[TBLOPEN];
PRINT["*******"];
If[ListQ[TBLPROCESSED]&&ListQ[TBLPROCESSED[[2]]]&&(And@@ListQ/@#&&Equal@@Length/@#&@(TBLPROCESSED[[2]])), 
(* TBL OPEN, SEPARATOR AND CLOSE DEFAULTS *)
If[Length[TBLPROCESSED]>2, TBLOPEN=TBLPROCESSED[[3]], 
TBLOPEN="\\begin{tabular}{"~~StringJoin@Map["|c"&, TBLPROCESSED[[2]][[1]]]~~"|}\\hline"];
If[Length[TBLPROCESSED]>4, TBLSEP=TBLPROCESSED[[5]], TBLSEP="\\\\\\hline"];
If[Length[TBLPROCESSED]>3,  TBLCLOSE=TBLPROCESSED[[4]], TBLCLOSE="\\\\\\hline\\end{tabular}"];
Join[TBLPROCESSED[[1;;2]], {TBLOPEN~~StringJoin@Flatten@Riffle[Map[Riffle[(("\\("~~ToString[#]~~"\\)")&)/@#, "&"]&, TBLPROCESSED[[2]]], TBLSEP]~~TBLCLOSE}]
,
{TBL, Null, Null}
]
];



(******************************************************************************)
(*   TEXT ANALYSIS FUNCTIONS (TO ANALIZE DIRECTLY FROM LATEX - TENTATIVE)   *)
(******************************************************************************)

PARAGRAPHS:=Function[TEXT,Map[ StringReplace[#,{"\n"->" ", "\t"->" "}]&, StringSplit[TEXT,Longest["\n"~~Whitespace...~~"\n"]]]];

SENTENCES:=StringSplit[#,"."|"?"|"!"]&;

(*****************************************************)
(* CLEANING AND EQUATION PROCESSING - NEW VERSION   *)
(*****************************************************)

LATEXOTHERCLEANER:=StringReplace[StringReplace[#, Shortest["\\hbox{"~~(arg1__/;balancedBracesQ[arg1])~~"}"]->""],{Shortest["\\begingroup"~~__~~"\\endgroup" ]->"[1]","\\usepackage{subcaption}"->"", "\\usepackage{showkeys}"->"", "\\usepackage{refcheck}"->"",Shortest["\\begin{figure}"~~__~~"\\end{figure}" ]->"",
Shortest["\\begin{verbatim}"~~__~~"\\end{verbatim}" ]->"", Shortest["\\verb"~~(x_~~___~~x_/;Not[LetterQ[x]])]->"",
Shortest["\\pause" ]->"",  "\\eqref{}"->"[1]", "\\ref{}"->"[1]", "\\cite{}"->"[1]",Shortest["\\cite{"~~__~~"}" ]->"[1]",Shortest["\\ref{"~~__~~"}" ]->"[1]",Shortest["\\eqref{"~~__~~"}" ]->"[1]","\\begin{proof}"->"", "\\end{proof}"->"" ,Shortest["\\begin{tabular}"~~__~~"\\end{tabular}" ]->"[1]","\\sc "->"","\\it "->"","\\bf "->""}]&;

FORMULASPATTERNS:={Shortest["\\["~~__~~"\\]" ],Shortest["\\("~~__~~"\\)" ],Shortest["\\begin{equation}"~~__~~"\\end{equation}" ],Shortest["\\begin{equation*}"~~__~~"\\end{equation*}" ],Shortest["\\begin{mathequation}"~~__~~"\\end{mathequation}" ],Shortest["\\begin{mathequation*}"~~__~~"\\end{mathequation*}" ],
 Shortest["\("~~__~~"\)" ],Shortest["\\begin{align}"~~__~~"\\end{align}" ],
Shortest["\\begin{align*}"~~__~~"\\end{align*}" ],Shortest["\\begin{eqnarray}"~~__~~"\\end{eqnarray}" ],Shortest["\\begin{displaymath}"~~__~~"\\end{displaymath}" ],Shortest["\\begin{eqnarray*}"~~__~~"\\end{eqnarray*}" ],Shortest["\\begin{multline}"~~__~~"\\end{multline}" ],Shortest["\\begin{multline*}"~~__~~"\\end{multline*}" ]};

Checkfirstthree=If[StringTake[#,3]=="[1]",#,"[1]"]&;

FORMULAPUNCTUATIONCLEANER2:=Checkfirstthree@StringReplace[#,(__~~Shortest[(x:"."|","|";")~~(Whitespace|"\n"|"\r\n"|""|"\\end{aligned}"|"\\end{cases}"|"\\end{split}")..~~(z:"\\]"|"\\)"|"\\end{gather}"|"\\end{gather*}"|"\\end{equation}"|"\\end{equation*}"|"\\end{align}"|"\\end{align*}"|"\\end{multline}"|"\\end{multline*}"|"\\end{eqnarray}"|"\\end{eqnarray*}"|"\\end{mathequation}"|"\\end{mathequation*}")])->"[1]"~~x]&;

FORMULASPLITRULES:=Map[formula:#->{formula,"[1]"}&,FORMULASPATTERNS];

(* NOW WE NEED TO CREATE THE CLEANUP FOR THE OTHER THINGS AS A SEPARATE FUNCTION - include verbatim there *)


(**************************)
(* BASIC LATEX VALIDATION *)
(**************************)

LATEXSANITYCHECK[TXT_]:=
Module[{beg,end}, 
beg=StringCount[TXT,"\\begin{document}"];
end=StringCount[TXT,"\\end{document}"];
If[beg>1||end>1, Print["Latex sanity check warning: multiple \\begin{document} or \\end{document} in the file"]];
If[beg==0||end==0, Print["no \\begin{document} or \\end{document}"]; Return[False]];
If[!balancedBracesQ[TXT], Print["Latex sanity check warning: unbalanced braces {}"]];
If[!StringContainsQ[TXT, "\\documentclass"], Print["Latex sanity check warning: no documentclass found"]];
True
];

MatchingEnvQ:=
Function[TXTD, (Length@Map[#[[1]]&, 
Select[Tally@Join[Tally@Sort@StringCases[TXTD,  Shortest["\\begin{"~~x:__~~"}"]->x],
Tally@Sort@StringCases[TXTD, Shortest["\\end{"~~x:__~~"}"]->x]], #[[2]]==1&]])===0];


BASICLATEXVALIDATION[TXTDOC_]:=
Module[
{NonMatchingEnvironments, BalBrace, MatchingFormulasA, MatchingFormulasB}, 

(* checks if environments are opening and closing *)

NonMatchingEnvironments=MatchingEnvQ[TXTDOC];

(* checks if all brackets close *)

BalBrace=balancedBracesQ[TXTDOC];

(* check if \[ closes with \] *)

MatchingFormulasA=Length@Map[#[[1]]&, Select[Tally@Join[Tally@Sort@StringCases[TXTDOC,   ((x_/;(x!="\\"))~~"\\[")->("\\[...\\]")],Tally@Sort@StringCases[TXTDOC,"\\]"->"\\[...\\]"]], #[[2]]==1&]]==0;

MatchingFormulasB=(StringCount[TXTDOC,  "\\("]==StringCount[TXTDOC,  "\\)"]);


(* Length@Map[#[[1]]&, Select[Tally@Join[Tally@Sort@StringCases[TXTDOC,  "\\("->"\\(...\\)"],Tally@Sort@StringCases[TXTDOC,"\\)"->"\\(...\\)"]], #[[2]]==1&]]==0; *)

(* outputs errors if any *)

Print["Matching environments: ", NonMatchingEnvironments];
If[!NonMatchingEnvironments,
Print[Grid[
Map[#[[1]]&, Select[Tally@Join[Tally@Sort@StringCases[TXTDOC,  Shortest["\\begin{"~~x:__~~"}"]->x],Tally@Sort@StringCases[TXTDOC, Shortest["\\end{"~~x:__~~"}"]->x]], #[[2]]==1&]], Frame->All]]
];
Print["Balanced braces {}: ", BalBrace];
Print["Matching formulas \\[...\\]: ", MatchingFormulasA]; 
Print["Matching formulas \\(...\\): ", MatchingFormulasB];

(* Warnings *)

If[StringContainsQ[TXTDOC, "\\epsilon"]&&StringContainsQ[TXTDOC, "\\varepsilon"],
Print["Warning: \\epsilon and \\varepsilon are used in the same document; possible mismatch?"]];

If[StringContainsQ[TXTDOC, "\\rho"]&&StringContainsQ[TXTDOC, "\\varrho"],
Print["Warning: \\epsilon and \\varepsilon are used in the same document; possible mismatch?"]];

If[StringContainsQ[TXTDOC, "\\to"~~(" "|"\\")]&&StringContainsQ[TXTDOC, "\\mapsto"~~(" "|"\\")],
Print["Warning: \\to and \\mapsto are used in the same document; possible mismatch?"]];


NonMatchingEnvironments&&BalBrace&&MatchingFormulasA&&MatchingFormulasB

];

(******************************)
(* TEXT ANALYSIS              *)
(******************************)

(* Problem parts of speech *)

HEDGINGandVAGUE=TextWords/@{"almost","a lot of","and so on","apparently","appears","appears to be","appear to be","appropriate","approximately","are sure","arguably","assume","believe","be sure","comparatively","conceivably","could be the case that","doubt","etc","fairly","feel","frequently", "generally", "in general", "has been generally agreed that","help","helps","hope","hopeful","hopefully","if true","indicate","indicates","in part","is generally agreed that","is important to develop","is sure","is useful to study","like","likely","look","looks","may","may be possible","may be possible to obtain","may be the case that","might","might be suggested that","my view","nearly","occasionally","often","our view","partially","perhaps","possibility","possible","possibly","practically","predominantly","presumably","probable","rather","reasonable","reckon","relatively","reportedly","roughly","seem","seemingly","seems","should","sometimes","somewhat","sort of","so to speak","stuff","suggest","suggests","suitable","tend","tends","there is every hope that","there is every hope that","thing","things like that","things like this","think","this kind","to a certain degree","to our knowledge","to some extent","type of","unlikely","usually","vague","virtually","whatever","whenever","wherever","whichever","whoever","would","would argue"};
INTENSIFIERS=TextWords/@{"completely","extremely","highly","novel","quite","really","totally","very"};
CLICHES=TextWords/@{"bread and butter","change the subject","changing the subject","for the first time","game changer","give and take","give or take","look at the facts","looking at the facts","novel","the long and the short"};
ABSTRACTNAMES=TextWords/@{"framework","issues","level","model","perspective","prospects","strategy"};
WORDINESS=TextWords/@{"are allowed", "is allowed", "absolute","actually","already","alternative","as a matter of fact","as the ability to","at such time as","at that point in time","at the present time","at this point in time","based on the fact that","basically","brought about the organization of","call your attention to the fact that","certain","complete","completely","continue to","despite the fact that","due partly to the fact that","due to the fact that","during the course of","empty","equal","eternal","extremely","fact of the matter","for the purpose of","has the potential to","have a facilitative impact","have the ability to","I might add that","in light of the fact that","in order","in order to","in spite of the fact that","in the event that","in the final analysis","in the matter of","in the vicinity of","in view of the fact that","is able to","is capable of being","is dedicated to providing","it is imperative that we","it is noteworthy","it is often the case that","it is significant that","it should be noted","it should be pointed out that","kind of","less","make an appearance with","make use", "make use of", "more","on a daily basis","on a weekly basis ","or the same ","owing to the fact that ","perfect ","practically ","previously ","quite ","really ","relating to the subject of ","relatively ","significantly expedite the process of ","somewhat ","still ","take under consideration ","the course of ","the fact that ","the presence of ","the question as to whether ","the reason is ","the reason why ","there is no doubt but that ","this is a subject that ","to be of the opinion ","to make reference to ","unique ","until such a time as ","very ","were in great need of ","which is ","which was ","who is ","who was ","widely observed that "};

StringContainsPart[text_,list_]:=Select[Map[If[Or@@(Length@SequenceCases[text, #]>0),#]&, list], !(#===Null)&];

(*readibility*)

ARI[ch_,wd_,st_]:=If[wd>0, 4.71*ch/wd+0.5*wd/st-21.43,0];

(* Coleman-Liau index - estimated *)

CLI[ch_,wd_,st_]:=If[wd>0,0.0588*ch/wd*100-0.296*st/wd*100-15.8,0];

(* Smog index - estimated *)

SMOG[wds_,st_]:= 1.0430*Sqrt[30*Length[Select[StringLength[wds],#>6&]]/st]+3.1291;

(* Glue index *)

Glue[txt_,wd_]:=If[wd>0, N[1-Length[TextWords[DeleteStopwords[txt]]]/wd],0];

(*has verb*)

HasVerb[sentencewords_]:=MemberQ[Flatten[Map[WordData[#,"BaseForm"]&,sentencewords]],"Verb"];

(* process text splits the text into sentences, and outputs a list with the following: original sentence, lower case sentence without [1]'s, words, #words, #chars , {ARI, CLI, SMOG, GLUE, # of words}, {HEDGING AND VAGUE, INTENSIFIERS, CLICHES, ABSTRACTNAMES, WORDINESS}, HASVERB *)

ProcessText[txt_]:=Map[Join[#,{{ARI[#[[5]],#[[4]],1], CLI[#[[5]],#[[4]],1], SMOG[#[[3]],1], Glue[#[[2]],#[[4]]]},{StringContainsPart[#[[3]],HEDGINGandVAGUE], 
StringContainsPart[#[[3]],INTENSIFIERS], StringContainsPart[#[[3]],CLICHES], 
StringContainsPart[#[[3]],ABSTRACTNAMES], StringContainsPart[#[[3]],WORDINESS]},HasVerb[#[[3]]]}]&, Map[Join[#, {Length[#[[3]]], StringLength[#[[2]]]}]&,Map[With[{LC=StringReplace[ToLowerCase@#, "[1]"->""]}, {#, LC, TextWords@LC}]&,TextSentences[
StringReplace[txt,{Whitespace..~~"."->".", Whitespace..->" "}]
]]]];

GenAnnLaTeX[Ptxt_]:=With[
{quants=Quantile[#,93/100]&/@ Transpose@Map[#[[6]]&, Ptxt]}, 
Map[
With[{
P0=(#[[4]]>20),  (* long sentence *)
P1=(#[[6]][[1]]>quants[[1]]||#[[6]][[2]]>quants[[2]]||#[[6]][[3]]>quants[[3]]), (* hard to read *)
P2=(#[[6]][[4]]>quants[[4]]||#[[6]][[4]]>0.8), (* high glue sentences *)
P3=(Union@Flatten@#[[7]]!={}),
P4=!#[[8]]
},
If[P0||P1||P2||P3||P4,"\n\n\\noindent {\\color{green} ********************}\n\n
\\noindent {\\color{red} "," "]~~
If[P0," {\\color{blue} (Long sentence) } ",""]~~
If[P1," {\\color{blue} (Low readability) } ",""]~~
If[P2," {\\color{blue} (High-glue sentence) } ",""]~~
If[P3," {\\color{blue} (Style problems: } "~~" {\\color{green} "~~
If[#[[7]][[1]]!={}, " {\\bf Hedging and Vague}: "~~StringJoin[Riffle[(StringJoin[Riffle[#, " "]]&)/@#[[7]][[1]], ", "]]~~"; ", ""]~~
If[#[[7]][[2]]!={}, " {\\bf Intensifiers}: "~~StringJoin[Riffle[(StringJoin[Riffle[#, " "]]&)/@#[[7]][[2]], ", "]]~~"; ", ""]~~
If[#[[7]][[3]]!={}, " {\\bf Cliches}: "~~StringJoin[Riffle[(StringJoin[Riffle[#, " "]]&)/@#[[7]][[3]], ", "]]~~"; ", ""]~~
If[#[[7]][[4]]!={}, " {\\bf Abstract names}: "~~StringJoin[Riffle[(StringJoin[Riffle[#, " "]]&)/@#[[7]][[4]], ", "]]~~"; ", ""]~~
If[#[[7]][[5]]!={}, " {\\bf Wordiness}: "~~StringJoin[Riffle[(StringJoin[Riffle[#, " "]]&)/@#[[7]][[5]], ", "]]~~"; ", ""]~~
"} {\\color{blue} ) } ", ""]~~
If[P4, " {\\color{blue} (No verb) }", ""]~~If[P0||P1||P2||P3||P4,"\n\n\\noindent ",""]~~#[[1]]~~If[P0||P1||P2||P3||P4,"}\n\n\\noindent {\\color{green} ********************}\n\n\\noindent "," "]
]&, Ptxt]];

(* Sentence complexity analysis functions *)


(* Relative entropy - using words rather than characters*)

RelEntro[Sen1_,Sen2_]:=
With[
{
n1=Length[TextWords[Sen1]],
n2=Length[TextWords[Sen2]],
wordcount1=Tally[TextWords[Sen1]],
commonwords=Select[Tally[TextWords[Sen1]],
MemberQ[Transpose[Tally[TextWords[Sen1]]][[1]],#[[1]]]&]
},
-Total[MapThread[#1[[2]]/n1 Log[#1[[2]]/#2[[2]] n2/n1]& ,{wordcount1,commonwords}]]//N];

(* Repetition word index *) 

RepWord[txt_]:=N[1-(Length@Union@TextWords@txt)/(Length@TextWords@txt)];

(* Gunning fog formula - TO BE IMPLEMENTED *)




BasicTextStatistics[txt_]:=
Module[{Txtnf, sen, txtwords, characters, words, sentences, WF, TXTNOSTOP, WF2},
Txtnf=StringReplace[StringReplace[txt,{","->"","[1]"->""}],{Whitespace..~~"."->".", Whitespace..->" "}]; (*removes multiple spaces and spaces before "."*)
sen=TextSentences[Txtnf];
txtwords=TextWords[Txtnf];
characters=Total[StringLength[txtwords]];
words=Length@txtwords;
sentences=Length[sen];
WF=WordCounts[ToLowerCase[StringReplace[Txtnf, {"[1]"->""}]]];
TXTNOSTOP=DeleteStopwords[ToLowerCase[StringReplace[Txtnf, {"[1]"->""}]]];
WF2=WordCounts[TXTNOSTOP];
Grid[{
{"Language = ",LanguageIdentify[Txtnf]}, 
{"Sentiment = ", Classify["Sentiment",Txtnf]},
{"# Characters = ", characters}, {"# Words = ",words}, 
{"# Sentences = ",sentences}, 
{"# Words/Sentence = ",N @ (words/sentences)},
{"# Distinct words = ",Length[Keys[WF]]},
{"# Distinct words (without stop words) = ",Length[Keys[WF2]]},
{"Automated Readibility index = ", ARI[characters,words,sentences]},
{"Coleman-Liau index = ",CLI[characters,words,sentences]},
{"SMOG grade = ",SMOG[txtwords, sentences]},
{"Glue index = ", Glue[Txtnf, words]},
{"Word repetition index = ", RepWord[Txtnf]}
}, Frame->All, Alignment->Left]
];

BasicTextStatisticsTex[txt_]:="\\section{Basic Text Statistics}\n \\["<>ToString@TeXForm@BasicTextStatistics[txt]<>"\\]\n\n";


TextStatisticalInformation[txt_]:=
Module[{Txtnf, sen, txtwords, characters, words, sentences, WF, TXTNOSTOP, WF2},
Txtnf=StringReplace[StringReplace[txt,{","->"","[1]"->""}],{Whitespace..~~"."->".", Whitespace..->" "}]; (*removes multiple spaces and spaces before "."*)
sen=TextSentences[Txtnf];
txtwords=TextWords[Txtnf];
characters=Total[StringLength[txtwords]];
words=Length@txtwords;
sentences=Length[sen];
WF=WordCounts[ToLowerCase[StringReplace[Txtnf, {"[1]"->""}]]];
TXTNOSTOP=DeleteStopwords[ToLowerCase[StringReplace[Txtnf, {"[1]"->""}]]];
WF2=WordCounts[TXTNOSTOP];
Association[
{"Characters"->characters, "Words"->words, 
"Sentences"->sentences, 
"Words per Sentence"->N @ (words/sentences), 
"Distinct words"->Length[Keys[WF]],
"Distinct words (without stop words)"->Length[Keys[WF2]],
"ARI"->ARI[characters,words,sentences],
"Coleman-Liau"->CLI[characters,words,sentences],
"SMOG"->SMOG[txtwords, sentences],
"Glue"->Glue[Txtnf, words],
"Word repetition"->RepWord[Txtnf]
}
]
];










(* EQUATION VALIDATION *)

latexcommandpattern=("int"|"kappa"); (*very incomplete!!*)
(* one idea is to extract all commands in use and then use them to check for possible mistakes *)
notbar[x_]:=x!="\\"


EquationValidation[Eq0_?StringQ]:=
Module[{Errors, possiblecommands, Eq},

(*clean-up labels and mboxes*)

Eq=StringReplace[Eq0, {Shortest["\\label{"~~(x___/;balancedBracesQ[x])~~"}"]->" ", Shortest["\\mbox{"~~(x___/;balancedBracesQ[x])~~"}"]->" "}];


Errors="\n\n  Equation errors and warnings:";

(* balanced parenthesis, braces, etc *)

If[!balancedBracesQ[Eq], Errors=Errors<>"\n\n Unbalanced $\\{\\}$"];
If[StringCount[Eq,"["]!=StringCount[Eq,"]"],  Errors=Errors<>"\n\n Unbalanced $[]$"];
If[StringCount[Eq,"("]!=StringCount[Eq,")"],  Errors=Errors<>"\n\n Unbalanced $()$"];
If[!EvenQ[StringCount[Eq,"|"]],  Errors=Errors<>"\n\n Unbalanced $|\\hdots|$"];
If[!EvenQ[StringCount[Eq,"\\|"]],  Errors=Errors<>"\n\n Unbalanced $\\|\\hdots\\|$"];
If[StringCount[Eq,"\\left"~~(x_/;Not[LetterQ[x]])]!=StringCount[Eq,"\\right"~~(x_/;Not[LetterQ[x]])],  Errors=Errors<>"\n\n Unbalanced \\verb1\\left...\\right1"];
If[StringCount[Eq,"\\begin{"]!=StringCount[Eq,"\\end{"],  Errors=Errors<>"\n\n Unbalanced \\verb1\\begin...\\end1"];

(* duplicate stuff *)

If[StringCount[Eq, "+"~~Whitespace...~~"+"]>0,Errors=Errors<>"\n\n Possibly duplicate $+$"];
If[StringCount[Eq, "-"~~Whitespace...~~"-"]>0,Errors=Errors<>"\n\n Possibly duplicate $-$"];
If[StringCount[Eq, "="~~Whitespace...~~"="]>0,Errors=Errors<>"\n\n Possibly duplicate $=$"];
If[StringCount[Eq, "/"~~Whitespace...~~"/"]>0,Errors=Errors<>"\n\n Possibly duplicate $/$"];

(* functions improperly used - need to add inverse trig + hyperbolic*)

If[StringCount[Eq, "Sin"]>0,Errors=Errors<>"\n\n $Sin$ or $\\sin$?"];
If[StringCount[Eq, "Cos"]>0,Errors=Errors<>"\n\n $Cos$ or $\\cos$?"];
If[StringCount[Eq, "Tan"]>0,Errors=Errors<>"\n\n $Tan$ or $\\tan$?"];
If[StringCount[Eq, "Log"]>0,Errors=Errors<>"\n\n $Log$ or $\\log$?"];
If[StringCount[Eq, "Ln"]>0,Errors=Errors<>"\n\n  $Ln$ or $\\ln$?"];

(* commonly confused stuff *)

If[StringContainsQ[Eq, "\\epsilon"]&& StringContainsQ[Eq, "\\varepsilon"],  Errors=Errors<>"\n\n  Formula contains $\\epsilon$ and $\\varepsilon$"];

If[StringContainsQ[Eq, "\\rho"]&& StringContainsQ[Eq, "\\varrho"], Errors=Errors<>"\n\n  Formula contains $\\rho$ and $\\varrho$"];

If[StringContainsQ[Eq, "\\omega"]&& StringContainsQ[Eq, "\\varomega"], Errors=Errors<>"\n\n  Formula contains $\\omega$ and $\\varomega$"];

If[StringContainsQ[Eq, "\\theta"]&& StringContainsQ[Eq, "\\vartheta"], Errors=Errors<>"\n\n  Formula contains $\\theta$ and $\\vartheta$"];

If[StringContainsQ[Eq, "\\phi"]&& StringContainsQ[Eq, "\\varphi"], Errors=Errors<>"\n\n  Formula contains $\\phi$ and $\\varphi$"];


(* more fancy commonly confused stuff *)

(* \to and \mapsto using pattern ___:___\mapsto___*)

If[StringContainsQ[Eq, ___~~":"~~___~~"\\mapsto"], Errors=Errors<>"\n\n  $\\mapsto$ used instead of $\\to$ "];

(* \frac in between parentesis - because we need \left( \right) to make it look nice*)

(* k and \kappa, v and \nu, u and \upsilon *)

(* integrals without domains *)

(* integral with dx but without balanced brackets in between *)

(* limits, series and sums without domains ?? *)


(* possible commands without \ before - need to create a comprehensive
command pattern list in latexcommandpattern*)

possiblecommands=StringCases[Eq, (x_/;notbar[x])~~latexcommandpattern];

If[Length@possiblecommands>0, Errors=Errors<>"\n\n possible command(s) not preceeded by backslash: "~~ StringJoin@Riffle[possiblecommands, ","]];


(* *)

Errors=Errors<>"}";

If[Errors=="\n\n  Equation errors and warnings:}", Eq0, "{\\color{red} "~~Eq0~~Errors~~"\n\n"]
]

FORMULASCHECKRULES=Map[formula:#:>EquationValidation[formula]&,FORMULASPATTERNS];

(*****************************************)
(** EXTRACTING VARIABLES FROM FORMULAS **)
(*****************************************)

mboxclean[str_?StringQ]:=StringReplace[str, Shortest[("\\mbox"|"\\text")~~"{"~~(z1__/;balancedBracesQ[z1])~~"}"]->" "];
labelclean[str_?StringQ]:=StringReplace[str, Shortest["\\label{"~~(z1__/;balancedBracesQ[z1])~~"}"]->" "];
begendclean[str_?StringQ]:=StringReplace[str,Shortest[("\\begin{array}{"|"\\begin{"|"\\end{")~~(z1__/;balancedBracesQ[z1])~~"}"]->" "];
funcclean[str_?StringQ]:=StringReplace[str, "\\sin"| "\\cos"|"\\tan"|"\\cotan"|"\\arctan"|"\\arcsin"|"\\arccos"|"\\ln"|"\\log"|"\\sqrt"|"e^"|"\\sinh"|"\\cosh"->" "];
symclean[str_?StringQ]:=StringReplace[str,(("\\left"|"\\right" )~~("("|")"|"["|"]"|"|"|"."|"{"|"}"))
|"("|")"|"["|"]"|"|"|"."|","|";"|":"|"~"|"<"|">"|("\\leq"~~(x_/;!LetterQ[x]))|
("\\geq"~~(x_/;!LetterQ[x]))|"!"|"\\@"|"@"|"#"|"\\%"|"\\&"|"*"|"{"|"}"|"^"|"$"|"="->" "];opclean[str_?StringQ]:=StringReplace[str,{Shortest[(("\\int"|"\\sum"|"\\oint")~~("_"|"^")~~"{"~~(z1__/;balancedBracesQ[z1])~~"}"~~("_"|"^")~~"{"~~(z2__/;balancedBracesQ[z2])~~"}")]:>" "~~z1~~" "~~z2, 
Shortest[(("\\int"|"\\sum"|"\\oint")~~"_{"~~(z1__/;balancedBracesQ[z1])~~"}^")]:>" "~~z1~~" ",
"\\frac"->" "}];
greekQ[x_?StringQ]:=MatchQ[x,"alpha"|"beta"|"gamma"|"Gamma"|"delta"|"Delta"|"epsilon"|"varepsilon"|"zeta"|"eta"|"theta"|"vartheta"|"Theta"|"iota"|"lambda"|"Lambda"|"nu"|"xi"|"Xi"|"pi"|"Pi"|"rho"|"varrho"|"tau"|"sigma"|"Sigma"|"upsilon"|"Upsilon"|"phi"|"varphi"|"Phi"|"chi"|"psi"|"Psi"|"omega"|"Omega"|"kappa"|"mu"];
commandcleanA[str_?StringQ]:=StringReplace[str, Longest["\\"~~x__/;LetterQ[x]]~~"_":>If[greekQ[x], "\\"~~x~~"_"," "]];
commandclean[str_?StringQ]:=StringReplace[str, Longest["\\"~~x__/;LetterQ[x]]:>If[greekQ[x], "\\"~~x," "]];
numberremover[str_?StringQ]:=StringReplace[str," "~~NumberString~~(" "|"\\ ")->" "];
whitespaceclean[str_?StringQ]:=StringReplace[str,Whitespace->" "];
whitespaceescaper[str_?StringQ]:=StringReplace[str, " "->" \\  "];
loseunderscoreandstuff[str_?StringQ]:=
StringReplace[
StringReplace[str, ("_ "|" + "|" - "|" +\\ "|" -\\ "|" _"|"+_"|"-_")->"\\  "], 
((x_/;LetterQ[x])~~("+"|"-"))->(x~~"\\ ")];

cleanform[str_?StringQ]:=loseunderscoreandstuff@whitespaceescaper@numberremover@commandclean@commandcleanA@FixedPoint[
whitespaceclean@symclean@funcclean@opclean@begendclean@labelclean@#&, mboxclean@str];

FORMULAVARIABLES=Variables@ToExpression[cleanform[#],TeXForm]&;

VarlistToString[NV_]:=StringReplace[StringJoin[(("\\("~~#~~"\\), ")&/@(ToString/@TeXForm/@NV))],
Shortest["\\unicode{"~~___~~"}"]->" "];
NewVariablesComment[B_]:=
Module[{AAux, BAux, Vars},

Print["Variables analysis"];


AAux={};
BAux=B;
Vars={};



While[BAux!={}, 

If[StringQ[First[BAux]], 

AAux=Join[AAux, {First[BAux]}];
BAux= Rest[BAux];, 

With[
{NV=Select[Complement[(First@BAux)[[2]],Vars], !(#===$Failed)&]},

If[NV=={},

AAux=Join[AAux, {First@First[BAux]}];
BAux=Rest[BAux];,

AAux=Join[AAux, { First@First[BAux]~~"\n{\\color{blue} New variable(s): "~~ VarlistToString[NV]~~" }\n"}];
BAux= Rest[BAux];
Vars= Join[Vars, NV];

]
]
]
];
StringJoin[AAux]
]

(* REFERENCE ANALYSIS *)

ReferenceAnalysis[AUXNOMARKUPOR_]:=
Module[{txt, refs, refsprocessed, Otex, Ftex, LList, FF, AUXNOMARKUP},

Print["Reference Analysis"];

AUXNOMARKUP=StringReplace[RemoveDiacritics@AUXNOMARKUPOR, {"\\thlabel"->"\\label", "\\thref"->"\\ref"}];

txt=StringSplit[AUXNOMARKUP, {Shortest["\\ref{"~~__~~"}" ],Shortest["\\eqref{"~~__~~"}" ], Shortest["\\label{"~~__~~"}" ]}];
refs=StringCases[AUXNOMARKUP, {Shortest["\\ref{"~~__~~"}" ],Shortest["\\eqref{"~~__~~"}" ], Shortest["\\label{"~~__~~"}" ]}];

(* StringJoin@Riffle[txt, refs]\[Equal]AUXNOMARKUP *)

refsprocessed={#,
If[StringMatchQ[#,("\\ref{"~~__~~"}")|("\\eqref{"~~__~~"}" )], "R", "L"], 
StringReplace[StringReplace[ #,{"\\ref{"~~(x__)~~"}"->x, "\\eqref{"~~(x__)~~"}"->x, "\\label{"~~(x__)~~"}"->x}], Whitespace->""]}&/@ refs;


Otex=Riffle[txt, refsprocessed];
Ftex={};
LList={};

While[Otex!={}, 

FF=First[Otex];

If[StringQ[FF],

Ftex=Append[Ftex, FF],

If[FF[[2]]==="L",
LList=Append[LList, Last@FF];
Ftex=Append[Ftex, First@FF];
(*Print[LList]*)
,
If[MemberQ[LList,Last@FF], Ftex=Append[Ftex, First@FF],
(* Print["FF ref"];Print[Last@FF];*)
Ftex=Append[Ftex, First@FF~~"\n {\\color{red} Forward or undefined reference: \\begin{verbatim}"
~~First@FF~~"\\end{verbatim}.}\n"];
(*Print[Last[Ftex]];*)
]
];


];

Otex=Rest[Otex];

];

StringJoin@Ftex

]






(* THE MLATEX MAIN CODE *) 

MLaTeX[file_,OptionsPattern[{
Images->True,
MEquations->True,
AUXOp->True,
Boolean->True,
TextA->True,
CompileL->True,
CleanL->True,
HTML->True,
Equations->False,
Tables->True,
Movies->True,
DocumentClass->"other",
DeepClean->True,
PaperStructure->False,
Executable->True, 
Listings->True,
FormulasRecompute->False,
ImagesRecompute->False,
ExeRecompute->False, 
RasterizeImages->False,
TablesRecompute->False, (* if this option is false tables will not recompute unless code is changed *)
LaTeX->"", (* default latex installation directory *)
CTT->True  (* cell to tex installed - this needs to be reflected in instructions *)
}]]:=
Module[{
LaTeXDir,
LaTeXToPDF,
BibTeX,
HTLaTeX, 
images, mequations, aux, boolean, texta, html, equations, cleanL, compileL,
tables, movies, deepclean,documentclass, paperstructure,formulasrecompute,
imagesrecompute, tablesrecompute,FLNM, TXT,TXTOriginal,TXTVC,TXTNoMARKUPVC,  TXTPreamble,TXTDocument,
NCOMMRULES, TXTNoMARKUP,TXTPreambleA,TXTDocumentA,TXTPreambleB,TXTDocumentB,
PRE, ART, FRM, FRM2, FRMS,FRMS2,FRMP, FRMP2, FRMSIMPP, FRMSIMPS, FRMSIMP, PCFRM,  MOV,
IMG,IMG2, PCIMG,  TBL,TBL2, PCTBL,  FAZ, ELTX, ELTX2, MLTX, MLTX2, listings, executable, EXE, LST, PEX, 
TXTPreambleNoMARKUP,TXTDocumentNoMARKUP, rasterizeimages, installedcelltotex, PCEXE, EXE2, exerecompute, codes, codes2, labels, labels2, ALLFIGS, FIGS, ALLTABLES, ALLTABLES2, preamble, celltotextinput, celltotextoutputB, ALLMOVS, MOVS}, 

(* missing options: ART, Formulas *)

(* SET OPTIONS VALUES *)

(* test=OptionValue[VTest];  TESTING IS NOW GENERATED IN A SEPARATE NOTEBOOK *) 
images=OptionValue[Images];
rasterizeimages=OptionValue[Images];
mequations=OptionValue[MEquations];
aux=OptionValue[AUXOp];
boolean=OptionValue[Boolean];
texta=OptionValue[TextA];
html=OptionValue[HTML];
equations=OptionValue[Equations];
cleanL=OptionValue[CleanL];
compileL=OptionValue[CompileL];
tables=OptionValue[Tables];
movies=OptionValue[Movies];
deepclean=OptionValue[DeepClean];
documentclass=OptionValue[DocumentClass];
paperstructure=OptionValue[PaperStructure];
formulasrecompute=OptionValue[FormulasRecompute];
imagesrecompute=OptionValue[ImagesRecompute];
tablesrecompute=OptionValue[TablesRecompute];
exerecompute=OptionValue[ExeRecompute];
LaTeXDir=OptionValue[LaTeX];
listings=OptionValue[Listings];
executable=OptionValue[Executable];



installedcelltotex=OptionValue[CTT];


(*  VARIABLE ROAD MAP

TXTOriginal = as the name says
TXT=INCLUDEANDCLEAN[TXTOriginal];

TXTVC=StringReplace[TXT, {Shortest["\\begin{verbatim}"~~__~~"\\end{verbatim}"]\[Rule]"", Shortest["\\begin{lstlisting}"~~__~~"\\end{lstlisting}"]\[Rule]""]

TXTNoMARKUP=...MLaTeXMARKUPREMOVER[TXT]...
TXTNoMARKUPINCLUDE=BASICINCLUDEREMOVER @ BASICINCLUDE[TXTNoMARKUP]
TXTNoMARKUPINCLUDE-> Exported as CL

TXTNoMARKUPVC=...MLaTeXMARKUPREMOVER[TXTVC],

{TXTPreamble,TXTDocument}=PREAMBLEANDDOC[TXTVC]; 
TXTDocumentA:=FixedPoint[StringReplace[#, RULESX]&, TXTDocument];

{TXTPreambleNoMARKUP,TXTDocumentNoMARKUP}=PREAMBLEANDDOC[TXTNoMARKUPVC]; 
TXTDocumentANoMARKUP:=FixedPoint[StringReplace[#, RULESX]&, TXTDocumentNoMARKUP];
TXTA=StringJoin[TXTPreamble,"\\begin{document}\n", TXTDocumentA,"\n\\end{document}\n"]

AUXNOMARKUP=FORMULAFIXER@TXTDocumentANoMARKUP;
AUXNOMARKUP is used in basic latex validation + formulas check (transformed into TXTFORMULASCHECKED-> EXPORTED AS FC)+ 
MEquations and EQuations are extract from TXTDocumentA 

Environments are extracted from TXTVC


TXTCOMPUTEDMKUP -> Replaces markup in TXT by images -> EXPORTED AS CP




TXTNoMARKUPINCLUDEA=BASICINCLUDEREMOVER @ BASICINCLUDE@MLaTeXMARKUPREMOVER[TXTA]
{TXTPreambleB,TXTDocumentB} =PREAMBLEANDDOC[TXTNoMARKUPINCLUDEA];
TXTDOCUMENTFORMULACLEAN -> based upon TXTDocumentB

TXTNoformulas=TXTPreambleB<>TXTDOCUMENTFORMULACLEAN

NEWTXT= text version of the HTML version 
ANTTXT = annotated version of NEWTXT




*)


 (*CHECK IF FILES EXISTS AND IMPORT IT *)

If[FileExistsQ[file],
TXTOriginal=Import[file, "String"],
Print["File does not exist - abort."];
Return[]];

(* checking the latex installation *)

If[
$OperatingSystem!="Windows"
,
Which[
LaTeXDir==""&&DirectoryQ["/Library/TeX/Distributions/.DefaultTeX/Contents/Programs/texbin/"], LaTeXDir="/Library/TeX/Distributions/.DefaultTeX/Contents/Programs/texbin/",
LaTeXDir==""&&DirectoryQ["/Library/TeX/texbin/"], LaTeXDir="/Library/TeX/texbin/", 
LaTeXDir==""&&DirectoryQ["/usr/texbin/"], LaTeXDir="/usr/texbin/", 
LaTeXDir==""&&DirectoryQ["/usr/bin/"], LaTeXDir="/usr/bin/", 
!DirectoryQ[LaTeXDir], Print["LaTeX directory not found at "~~LaTeXDir~~" - Aborting."];Return[]
];
LaTeXToPDF=LaTeXDir~~"pdflatex";
If[!FileExistsQ[LaTeXToPDF], Print["pdflatex not found at "~~LaTeXToPDF~~" - Aborting."];Return[]];
BibTeX=LaTeXDir~~"bibtex";
If[!FileExistsQ[BibTeX], Print["bibtex not found at "~~BibTeX~~" - Aborting."];Return[]];
HTLaTeX=LaTeXDir~~"htlatex" ;
If[!FileExistsQ[HTLaTeX], Print["htlatex not found at "~~HTLaTeX~~" - Aborting."];Return[]];,

(* WINDOWS INSTALLATION *)
Which[
LaTeXDir==""&&DirectoryQ[""~~$HomeDirectory~~ "\\AppData\\Local\\Programs\\MiKTeX 2.9\\miktex\\bin\\"], LaTeXDir=""~~$HomeDirectory~~ "\\AppData\\Local\\Programs\\MiKTeX 2.9\\miktex\\bin\\", 
!DirectoryQ[LaTeXDir], Print["LaTeX directory not found at "~~LaTeXDir~~" - Aborting."];Return[]
];
LaTeXToPDF=LaTeXDir~~"pdflatex.exe";
If[!FileExistsQ[LaTeXToPDF], Print["pdflatex not found at "~~LaTeXToPDF~~" - Aborting."];Return[]];
BibTeX=LaTeXDir~~"bibtex.exe";
If[!FileExistsQ[BibTeX], Print["bibtex not found at "~~BibTeX~~" - Aborting."];Return[]];
HTLaTeX=LaTeXDir~~"htlatex.exe" ;
If[!FileExistsQ[HTLaTeX], Print["htlatex not found at "~~HTLaTeX~~" - Aborting."];Return[]];
];


(*

Which[
LaTeXDir==""&&DirectoryQ["/Library/TeX/texbin/"], LaTeXDir="/Library/TeX/texbin/";, 
LaTeXDir==""&&DirectoryQ["/usr/texbin/"], LaTeXDir="/usr/texbin/", 
!DirectoryQ[LaTeXDir], Print["LaTeX directory not found at "~~LaTeXDir~~" - Aborting."];Return[]
];
LaTeXToPDF=LaTeXDir~~"pdflatex";
If[!FileExistsQ[LaTeXToPDF], Print["pdflatex not found at "~~LaTeXToPDF~~" - Aborting."];Return[]];
BibTeX=LaTeXDir~~"bibtex";
If[!FileExistsQ[BibTeX], Print["bibtex not found at "~~BibTeX~~" - Aborting."];Return[]];
HTLaTeX=LaTeXDir~~"htlatex" ;
If[!FileExistsQ[HTLaTeX], Print["htlatex not found at "~~HTLaTeX~~" - Aborting."];Return[]];
*)

(* Latex sanity check *)

If[!LATEXSANITYCHECK[TXTOriginal], Print["Latex sanity fail"]; Return[], Print["Latex sanity check pass"]];


(* SETS THE WORKING DIRECTORY AND TAKES THE FILENAME*)

$BASEDIR=DirectoryName[file];
SetDirectory[$BASEDIR];
FLNM=FileNameTake[file];

(* fix spaces in filename, this is an issue in MAC-OS *)
(* need to figure out if this is an issue in Windows too *)

FLNM2=StringReplace[FLNM," "->"\\\ "];
FLNM3=StringReplace[FLNM, " "->""];


(* BASIC CLEAN MODE - CLEAN TEXT, REMOVE MARKUP, REPLACE NEW COMMANDS *)




TXT=INCLUDEANDCLEAN[TXTOriginal]; (* cleaned up text in the webversion BASICTEXTCLEAN[TXTOriginal]*)


TXTVC=
StringReplace[#, Shortest["\\verb"~~(x_)~~___~~(x_)]:>""]&@
StringReplace[#, Shortest["\\begin{SKIP}"~~__~~"\\end{SKIP}"]->""]&@
StringReplace[TXT, {Shortest["\\begin{verbatim}"~~__~~"\\end{verbatim}"]->"", Shortest["\\begin{lstlisting}"~~__~~"\\end{lstlisting}"]->""}];



If[!LATEXSANITYCHECK[TXTVC], Print["Latex sanity fail after cleaning - abort."]; Return[], Print["Latex sanity check pass after cleaning"]];



TXTNoMARKUP=StringReplace[MLaTeXMARKUPREMOVER[TXT], {"\\begin{SKIP}"->"", "\\end{SKIP}"->""}]; (* text without MLaTeX Markup - USED ONLY FOR THE CLEAN VERSION, no other processing here *)

TXTNoMARKUPVC=StringReplace[MLaTeXMARKUPREMOVER[TXTVC], {"\\begin{SKIP}"->"", "\\end{SKIP}"->""}]; (* text without MLaTeX Markup w/o verbatim or listings *)


{TXTPreamble,TXTDocument}=PREAMBLEANDDOC[TXTVC]; 
{TXTPreambleNoMARKUP,TXTDocumentNoMARKUP}=PREAMBLEANDDOC[TXTNoMARKUPVC]; 

If[StringContainsQ[TXTDocument, ("\\def"|"\\newcommand"|"\\renewcommand")~~(x_/;(!LetterQ[x]))],
Print["Warning: there are \\def or \\newcommand or \\renewcommand in the document body. If errors arise,
move them to the preamble"]];


(********** REPLACE NEW COMMANDS ****************)

RULESX= SORTNCOMMTORULES@NCOMMTORULES[NCOMEXTRACT[TXTPreamble]]; (* EXTRACT THE RULES AND SORT THEM FOR NICER PROCESSING *)

(*Print[NCOMEXTRACT[TXTPreamble]];*)

TXTDocumentA:=FixedPoint[StringReplace[#, RULESX]&, TXTDocument];



TXTDocumentANoMARKUP:=FixedPoint[StringReplace[#, RULESX]&, TXTDocumentNoMARKUP];



TXTA=StringJoin[TXTPreamble,"\\begin{document}\n", TXTDocumentA,"\n\\end{document}\n"];






AUXNOMARKUP=FORMULAFIXER@TXTDocumentANoMARKUP;



Print["Basic Latex Validation"];



If[BASICLATEXVALIDATION[AUXNOMARKUP], Print["Basic Latex Validation Pass"], Print["Basic Latex Validation Fail. Stopping."]; Return[]];

(* TXTOriginal = the original version of the file *)
(* TXT = original with all includes + comments removed *)
(* TXTNoMARKUP = TXT without the M-LaTeX Markup command ->used as basis for the clean version AFTER WE INCLUDE WHAT WE NEED LATER*)

(* TXTA = TXT with new commands replaced \[Rule] later we need to include the new includes \[Rule] this is the basis to extract equations AND for the annotated version AND for the no formulas version *)




(******* FORMULAS CHECKER ALGORITHM  *****)

(* STEP 1 *)

(* PAPER STRUCTURE ANALYSIS - DEEP ANALYSIS ONLY*)

(* STEP 2 *)

(* CHECK THE FORMULAS AND THEOREMS WITHOUT LABELS WITHOUT LABELS + DUPLICATED LABELS *)

AUXNOMARKUP3=ReferenceAnalysis[AUXNOMARKUP]; (* checks the reference structure *)


(* STEP 3 *)

(* INTRODUCED VARIABLES ANALYSIS - DEEP ANALYSIS ONLY *)

AUXNOMARKUP2=NewVariablesComment[Riffle[StringSplit[AUXNOMARKUP3, FORMULASPATTERNS],
{#, FORMULAVARIABLES[#]}&/@StringCases[AUXNOMARKUP3, FORMULASPATTERNS]]];


(* STEP 4 *)

(* CHECK FORMULAS CORRECTEDNESS *)



TXTFORMULASCHECKED=StringJoin[TXTPreambleNoMARKUP, "\\usepackage{color}\\begin{document}\n",
(* the next line is needed to remove verbatim inside caption or footnotes - apparently latex does not like it *)
StringReplace[#, Shortest[(z:("\\caption{"|"\\footnote{"))~~(x___/;balancedBracesQ[x])~~"}"]:> (z~~(StringReplace[x, Shortest["\\begin{verbatim}"~~___~~"\\end{verbatim}"]->" "])~~"}")]&@
StringReplace[AUXNOMARKUP2, FORMULASCHECKRULES]
, "\n\\end{document}\n"];



(* STEP 5 *) 

(* GLOBAL WARNINGS - \epsilon vs \varepsilon issues *)


(* END OF FORMULAS CHECKER ALGO *)


(* MARKUP EXTRACTION *)

(*EXTRACT MATHEQUATIONS - we extract everything because of the Label analysis*)


MLTX=Extractor[TXTDocumentA, {{"\\begin{mathequation}","\\end{mathequation}"}, {"\\begin{mathequation*}","\\end{mathequation*}"}}];
MLTX2=Extractor2[TXTDocumentA, {{"\\begin{mathequation}","\\end{mathequation}"}, {"\\begin{mathequation*}","\\end{mathequation*}"}}];

(*EXTRACT ALL LATEX EQUATIONS - here we are not extracting from multlines, splits, etc - should we?? YES *)


ELTX=Extractor[TXTDocumentA, {{"\\begin{equation}","\\end{equation}"},{"\\begin{equation*}","\\end{equation*}"},{"\\begin{displaymath}","\\end{displaymath}"}, {"$$","$$"},{"$","$"},{"\\[","\\]"},{"\\begin{align*}","\\end{align*}"},{"\\begin{align}","\\end{align}"}}];
ELTX2=Extractor2[TXTDocumentA, {{"\\begin{equation}","\\end{equation}"},{"\\begin{equation*}","\\end{equation*}"},{"\\begin{displaymath}","\\end{displaymath}"}, {"$$","$$"},{"$","$"},{"\\[","\\]"},{"\\begin{align*}","\\end{align*}"},{"\\begin{align}","\\end{align}"}}];

(* LIST ALL VARIABLES FROM EQUATIONS - FOR DEVELOPMENT ONLY 
Print[Grid[Transpose[{ELTX2, cleanform/@ELTX2, FORMULAVARIABLES/@ELTX2}], Frame->All]]; 
*)

(* Extract environments - these are extracted from the ORIGINAL text (with includes and  without comments) to avoid issues with the newcommands *)

(* We don't need to extract what does not need to be computed *)

(* Preamble *) 

PRE:= Extractor[TXTVC,  {{"\\begin{PRE}","\\end{PRE}"}}];

(* Auxiliary results *)

ART:= Extractor[TXTVC,  {{"\\begin{ART}","\\end{ART}"}}];



(* Function Analysis *)

FAZ:= Extractor[TXTVC,  {{"\\begin{FAZ}","\\end{FAZ}"}}];

(* Images *)

IMG:=Extractor[TXTVC,  {{"\\begin{IMG}","\\end{IMG}"}}];

(* Formulas *)

FRM:=Extractor[TXTVC,  {{"\\begin{FRM}","\\end{FRM}"}}];
FRMS:=Extractor[TXTVC,  {{"\\begin{FRM*}","\\end{FRM*}"}}];
FRMP:=Extractor[TXTVC,  {{"\\begin{FRMI}","\\end{FRMI}"}}];

(* MOVIE - TBD*)

If[movies, 

MOV:=Extractor[TXTVC,  {{"\\begin{MOV}","\\end{MOV}"}}];

];

(* TABLE ELEMENT  - TBD*)

If[tables, 

TBL:=Extractor[TXTVC,  {{"\\begin{TBL}","\\end{TBL}"}}];

];

(* Listings elements *)

If[listings, 

LST:=Extractor[TXTVC,  {{"\\begin{LST}","\\end{LST}"}}];

];


(* executable elements *)

If[executable, 

EXE:=Extractor[TXTVC,  {{"\\begin{EXE}","\\end{EXE}"}}];

];

(* preamble for executable elements *)

If[executable, 

PEX:=Extractor[TXTVC,  {{"\\begin{PEX}","\\end{PEX}"}}];

];


(* END OF MARKUP EXTRACTION *)

(* MARKUP SAFETY PROCESSING (MSP) - EXCLUDES ALL THAT OUTPUT, INPUT OR EXECUTE ARBITARY CODE *) 


(* END OF MSP *)

(* MARKUP PROCESSING *) 

(* COMPUTE PREAMBLE *)


CreateDirectory["computations"]//Quiet;
SetDirectory[DirectoryName[file]<>"/computations"]//Quiet;

(* PREAMBLE IS ALWAYS COMPUTED IF IT EXISTS *)

If[Length[PRE]>0,
Print["PREAMBLE"];
CPRE=ToExpression/@PRE;
Map[Export[ToString[Hash[#[[1]]]]~~".pdf", #, "PDF"]&, Transpose@{PRE, CPRE}];
Print[Grid[CPRE,Frame->All]];
]; 


(*COMPUTE AUXILIARY RESULTS*)

If[aux&&Length[ART]>0,
Print["AUXILIARY RESULTS"];
CART=FullSimplify/@ToExpression/@ART;
ART2=ART; (*DEBUG*)
Map[Export[ToString[Hash[#[[1]]]]~~".pdf", #, "PDF"]&, Transpose@{ART, CART}];Print[Grid[FullSimplify[ToExpression[ART]],Frame->All]];
]; 

SetDirectory[DirectoryName[file]]//Quiet;

(* GENERATE FORMULAS, IMAGES, AND MOVIES, *)

(*GENERATING FORMULAS FROM LATEX*)

If[Length@FRM+Length@FRMS+Length@FRMP>0,
Print["Generating formulas from LaTeX"];
SetDirectory[DirectoryName[file]];
CreateDirectory["formulas"]//Quiet;
SetDirectory[DirectoryName[file]<>"/formulas"]//Quiet;
PCFRM=If[FileExistsQ["precomputedformulas"]&&!formulasrecompute, Import["precomputedformulas", "Integer128"], {}];
];

If[Length@FRM>0,
FRM2=Select[FRM,!MemberQ[PCFRM, Hash[#]]& ];
PCFRM=Join[PCFRM, Map[Hash, FRM2]];
FRMSIMP=Map[{#[[1]],#[[2]], ToString [#[[2]]//TeXForm],ToString@Hash[#[[1]]]} & , Map[{ToExpression[#][[1]], FullSimplify[ToExpression[#][[2]]]}&, FRM2]];
Print[Grid[FRMSIMP, Frame->All]];
Map[Export[#[[1]], "\\begin{equation}\\label{"<>(ToString@Hash[#[[1]]])<>"}"<>#[[3]]<>"\\end{equation}","Text"]&,FRMSIMP];
];

If[Length@FRMS>0,
FRMS2=Select[FRMS,!MemberQ[PCFRM, Hash[#]]& ];
PCFRM=Join[PCFRM, Map[Hash, FRMS2]];
FRMSIMPS=Map[{#[[1]],#[[2]], ToString [#[[2]]//TeXForm]}& , Map[{ToExpression[#][[1]], FullSimplify[ToExpression[#][[2]]]}&, FRMS2]];
Print[Grid[FRMSIMPS, Frame->All]];
Map[Export[#[[1]], "\\begin{equation*}"<>#[[3]]<>"\\end{equation*}","Text"]&,FRMSIMPS]];

If[Length@FRMP>0,
FRMP2=Select[FRMP,!MemberQ[PCFRM, Hash[#]]& ];
PCFRM=Join[PCFRM, Map[Hash, FRMP2]];
FRMSIMPP=Map[{#[[1]],#[[2]], ToString [#[[2]]//TeXForm]}& , Map[{ToExpression[#][[1]], FullSimplify[ToExpression[#][[2]]]}&, FRMP2]];
Print[Grid[FRMSIMPP, Frame->All]];
Map[Export[#[[1]], "\\("<>#[[3]]<>"\\)","Text"]&,FRMSIMPP]];


If[Length@FRM+Length@FRMS+Length@FRMP>0,
Export["precomputedformulas", PCFRM, "Integer128"]
];

SetDirectory[DirectoryName[file]]//Quiet;

(* GENERATING TABLES *)

If[tables && (Length@TBL>0),
Print["Generating tables from LaTeX"];
SetDirectory[DirectoryName[file]];
CreateDirectory["tables"]//Quiet;
SetDirectory[DirectoryName[file]<>"/tables"]//Quiet;
PCTBL=If[FileExistsQ["precomputedtables"]&&!tablesrecompute, Import["precomputedtables", "Integer128"], {}];
TBL2=Select[TBL,!MemberQ[PCTBL, Hash[#]]& ];
PCTBL=Join[PCTBL, Map[Hash, TBL2]];

ALLTABLES=Map[MAKETABLE,TBL2];
ALLTABLES2=Select[ALLTABLES,!( #[[2]]===Null)&];

If[Length@ALLTABLES2>0, 
Print[Grid[Map[{#[[1]], Grid[#[[2]], Frame->All]}&, Transpose[Transpose[ALLTABLES2][[1;;2]]]], Frame->All]];
Map[Export[#[[1]], #[[3]], "Text"]&, ALLTABLES2];
];

Export["precomputedtables", PCTBL, "Integer128"]
];


(* END OF TABLE GENERATION *)

(* LISTINGS *)

SetDirectory[DirectoryName[file]]//Quiet;

If[listings && (Length@LST>0), 
Print["Generating listings"];
codes=StringCases[#, Longest["(*CODE*)"~~(x___)~~"(*CODE*)"]:>x]&/@LST;
labels=StringCases[#,Shortest["LABEL=\""~~x___~~"\""]:>x]&/@LST;
CreateDirectory["listings"]//Quiet;
SetDirectory[DirectoryName[file]<>"/listings"]//Quiet;
MapThread[If[#1!={}&&#2!={}, Export[First@#2~~".tex", 
"\\begin{lstlisting}"~~First@#1~~"\\end{lstlisting}", "Text"]]&, {codes, labels}];
];

SetDirectory[DirectoryName[file]]//Quiet;

(* EXECUTABLES *)

celltotextinput:=StringReplace[CellToTeX[Cell[BoxData[MakeBoxes[#]],"Input"]], Longest["Hold["~~x___~~"]"]:>x]&;
(*celltotextoutput:=CellToTeX[Cell[BoxData[MakeBoxes[#]],"Output"]]&;*)
celltotextoutputB:=Cell[BoxData[MakeBoxes[#]],"Output"]&;

If[executable && (Length@EXE>0), 
Print["Generating executables"];
preamble=StringJoin@@(StringCases[#, Longest["(*CODE*)"~~(x___)~~"(*CODE*)"]:>x]&/@PEX);
codes=StringCases[#, Longest["(*CODE*)"~~Whitespace~~(x___)~~"(*CODE*)"]:>x]&/@EXE;
labels=StringCases[#,Shortest["LABEL=\""~~x___~~"\""]:>x]&/@EXE;
(*punctuation=StringCases[#,Shortest["PUNCT={"~~x___~~","~~y___~~"}"]\[RuleDelayed]{x,y}]&/@EXE;*)
CreateDirectory["executables"]//Quiet;

PCEXE=If[FileExistsQ["executables/precomputedexe"]&&!exerecompute, Import["executables/precomputedexe", "Integer128"], {}];
EXE2=Select[{codes, labels}//Transpose,!MemberQ[PCEXE, Hash[#]]& ];
PCEXE=Join[PCEXE, Map[Hash, EXE2]];





codes2=EXE2[[All,1]];
labels2=EXE2[[All,2]];


SetDirectory[DirectoryName[file]<>"/executables"]//Quiet;
Export["precomputedexe", PCEXE, "Integer128"];
MapThread[If[#1!={}&&#2!={}, Export[First@#2~~".nb", preamble~~First@#1, "Text"]]&, {codes2, labels2}];
MapThread[If[#1!={}&&#2!={}, Export[First@#2~~"result.nb",InputForm@ToExpression[First@#1],"Text"]]&, {codes2, labels2}];
MapThread[If[#1!={}&&#2!={}, Export[First@#2~~".pdf", First@#1]]&, {codes2, labels2}];
MapThread[If[#1!={}&&#2!={}, Export[First@#2~~"result.pdf",ToExpression[First@#1]]]&, {codes2, labels2}];
If[installedcelltotex, 

MapThread[If[#1!={}&&#2!={}, Export[First@#2~~"ctt.tex", celltotextinput[ToExpression[First@#1, StandardForm, Hold]/.\[FormalCapitalC]->"C"],"Text"]]&, {codes2, labels2}];
MapThread[If[#1!={}&&#2!={}, Export[First@#2~~"ctt.result.tex",CellToTeX@celltotextoutputB[ToExpression[First@#1]/.\[FormalCapitalC]->"C"],"Text"]]&, {codes2, labels2}];

]

];


SetDirectory[DirectoryName[file]]//Quiet;



(*IMAGE CREATION*)

If[images&& (Length[IMG]>0),

Print["Generating images from LaTeX"];
CreateDirectory["figures"]//Quiet;
PCIMG=If[FileExistsQ["figures/precomputedimages"]&&!imagesrecompute, Import["figures/precomputedimages", "Integer128"], {}];
IMG2=Select[IMG,!MemberQ[PCIMG, Hash[#]]& ];
PCIMG=Join[PCIMG, Map[Hash, IMG2]];


ALLFIGS=Map[ToExpression,IMG2];

(* REMOVE NON IMAGES (AKA other auxiliary results) *) 

FIGS=Select[Select[ALLFIGS,ListQ],Head[#[[2]]]==Graph||Head[#[[2]]]==Legended||Head[#[[2]]]==Graphics||Head[#[[2]]]==Graphics3D&];

(* PRINT AND EXPORT *)

Print[Grid[FIGS, Frame->All]];

If[rasterizeimages, 

Map[Export["figures/"<>#[[1]]<>".pdf", #[[2]],"PDF"]&, FIGS];
Map[Export["figures/"<>#[[1]]<>".jpg", #[[2]],"JPG"]&, FIGS];
Map[Export["figures/"<>#[[1]]<>".eps", #[[2]],"EPS"]&, FIGS];
Map[Export["figures/"<>#[[1]]<>".tiff", #[[2]],"TIFF"]&, FIGS];, 

Map[Export["figures/"<>#[[1]]<>".pdf", #[[2]],"PDF", Rasterize[PlotmVls, RasterSize -> 1000], ImageSize -> 360, 
 ImageResolution -> 600]&, FIGS];
Map[Export["figures/"<>#[[1]]<>".jpg", #[[2]],"JPG", Rasterize[PlotmVls, RasterSize -> 1000], ImageSize -> 360, 
 ImageResolution -> 600]&, FIGS];
Map[Export["figures/"<>#[[1]]<>".eps", #[[2]],"EPS", Rasterize[PlotmVls, RasterSize -> 1000], ImageSize -> 360, 
 ImageResolution -> 600]&, FIGS];
 Map[Export["figures/"<>#[[1]]<>".tiff", #[[2]],"TIFF", Rasterize[PlotmVls, RasterSize -> 1000], ImageSize -> 360, 
 ImageResolution -> 600]&, FIGS]
];





Export["figures/precomputedimages", PCIMG, "Integer128"];

];


(*MOVIES*)
(* A movie is simply a table of images *)

If[movies&&(Length[MOV]>0),

Print["Generating movies from LaTeX"];
SetDirectory[DirectoryName[file]];
CreateDirectory["movies"]//Quiet;

ALLMOVS=Table[ToExpression[MOV[[i]]],{i,1,Length[MOV]}];

(* REMOVE NON MOVIES(AKA other auxiliary results) *) 

MOVS=Select[Select[ALLMOVS,ListQ],Head[#[[2]]]==List&];

(*  EXPORT *)
Print[Grid[Map[{#[[1]], ListAnimate[#[[2]]]}&, MOVS], Frame->All]];
Map[Export["movies/"<>#[[1]]<>".avi", #[[2]],"avi"]&, MOVS];

];



(* END OF MARKUP PROCESSING *)


(* GENERATE FILE WITH COMPUTED MARK-UP *)

	CreateDirectory["MLaTeX/artexecutables"] //Quiet;
	SetDirectory[DirectoryName[file]<>"MLaTeX/artexecutables"]//Quiet;
(*
TXTCOMPUTEDMKUP=StringReplace[TXTVC, 
{Shortest["\\begin{ART}"~~(x__)~~"\\end{ART}"]:>("\\begin{figure}\\centering\\includegraphics{computations/"~~ToString[Hash[x]]~~".pdf"~~"}
\\caption{ART RESULTS}\\label{"~~ToString[Hash[x]]~~"}\\end{figure}\n\n
{\\bf ART RESULTS IN FIGURE \\ref{"~~ToString[Hash[x]]~~"} - corresponding code
\\href{run:./artexecutables/"~~(Export[ToString[Hash[x]]~~".nb", x, "Text"];
ToString[Hash[x]])~~".nb}{here}}.\n\n")}];
*)


TXTCOMPUTEDMKUP=StringReplace[TXTVC, 
{
Shortest["\\begin{ART}"~~(x__)~~"\\end{ART}"]:>("{\\color{red} For the ART results click 
\\href[pdfnewwindow=true]{run:../computations/"~~ToString[Hash[x]]~~".pdf}{here} and for 
the corresponding code click 
\\href{run:./artexecutables/"~~(Export[ToString[Hash[x]]~~".nb", x, "Text"];
ToString[Hash[x]])~~".nb}{here}}.\n\n")
}];






	SetDirectory[DirectoryName[file]]//Quiet;

(*  *)

(* THIS PART OF THE CODE SHOULD ONLY RUN AFTER ALL MARKUP IS PROCESSED IN PARTICULAR IT WILL INCLUDE ALL GENERATED FORMULAS*)




TXTNoMARKUPINCLUDE=BASICINCLUDEREMOVER @ BASICINCLUDE[TXTNoMARKUP]; (* USED ONLY FOR THE CLEAN VERSION *)






(********************)
(********************)
(********************)
(********************)
(********************)
(********************)
(********************)
(************)

(******************* UNDER REVISION **************************)


TXTNoMARKUPINCLUDEA=BASICINCLUDEREMOVER @ BASICINCLUDE@MLaTeXMARKUPREMOVER[TXTA];(* USED FOR THE NO FORMULAS *)



(* GENERATE THE CLEAN DOCUMENT WITHOUT FORMULAS *)

{TXTPreambleB,TXTDocumentB} =PREAMBLEANDDOC[TXTNoMARKUPINCLUDEA];

(* clean up punctuation  - DISPLAY MATH MISSING *)



TXTDOCUMENTFORMULACLEAN=LATEXFORMULACLEANER[PUNCTUATIONCLEANER[StringReplace[TXTDocumentB,
Shortest["\\begin{SKIP}"~~___~~"\\end{SKIP}"]->" "]]];



(* returns the no formulas cleaned version of the paper *)




TXTNoformulas=
If[documentclass=="original", 
StringJoin[TXTPreambleB,"\\begin{document}\n", DEEPCLEAN[TXTDOCUMENTFORMULACLEAN,deepclean],"\n\\end{document}\n"], StringJoin["\\documentclass{article}\n\\begin{document}\n", DEEPCLEAN[TXTDOCUMENTFORMULACLEAN,deepclean],"\n\\end{document}\n"]];


(************************ END OF UNDER REVISION **********************)


(* EXPORTING FORMULA CHECKED *)

Print["Exporting formula checked version, FC"<>FLNM];
Export["FC"<>FLNM3,TXTFORMULASCHECKED,"Text"];

(* LaTeXToPDF, BibTeX, HTLaTeX *)

Run[LaTeXToPDF<>" FC"<>FLNM3];
Run[BibTeX<>" FC"<>StringReplace[FLNM3,".tex"->""]];
Run[LaTeXToPDF<>" FC"<>FLNM3];
Run[LaTeXToPDF<>" FC"<>FLNM3];

(*
Run["/Library/TeX/texbin/pdflatex FC"<>FLNM2];
Run["/Library/TeX/texbin/bibtex FC"<>StringReplace[FLNM2,".tex"->""]];
Run["/Library/TeX/texbin/pdflatex FC"<>FLNM2];
Run["/Library/TeX/texbin/pdflatex FC"<>FLNM2];

*)

(*EXPORTING FILES - CLEAN VERSION*)

If[cleanL,
(*EXPORT NOMARKUP VERSION AND COMPILE IT TO PDF*)

Print["Exporting clean version, CL"<>FLNM];
Export["CL"<>FLNM3,TXTNoMARKUPINCLUDE,"Text"];

];

(* COMPILATION *)

If[compileL, 

Print["COMPILING"];
Print["PDF - ", FLNM];

Run[LaTeXToPDF<>" "<>FLNM2];
Run[BibTeX<>" "<>StringReplace[FLNM2,".tex"->""]];
Run[LaTeXToPDF<>" "<>FLNM2];
Run[LaTeXToPDF<>" "<>FLNM2];

(*
Run["/Library/TeX/texbin/pdflatex "<>FLNM2];
Run["/Library/TeX/texbin/bibtex "<>StringReplace[FLNM2,".tex"->""]];
Run["/Library/TeX/texbin/pdflatex "<>FLNM2];
Run["/Library/TeX/texbin/pdflatex "<>FLNM2];
*)

If[cleanL,
(*EXPORT NOMARKUP VERSION AND COMPILE IT TO PDF*)
Print["Compiling clean version, CL"<>FLNM];

Run[LaTeXToPDF<>" CL"<>FLNM3];
Run[BibTeX<>" CL"<>StringReplace[FLNM3,".tex"->""]];
Run[LaTeXToPDF<>" CL"<>FLNM3];
Run[LaTeXToPDF<>" CL"<>FLNM3];
];
(*
Run["/Library/TeX/texbin/pdflatex CL"<>FLNM2];
Run["/Library/TeX/texbin/bibtex CL"<>StringReplace[FLNM2,".tex"->""]];
Run["/Library/TeX/texbin/pdflatex CL"<>FLNM2];
Run["/Library/TeX/texbin/pdflatex CL"<>FLNM2];
*)



Print["Exporting version with computations"];
Export["CP"<>FLNM,TXTCOMPUTEDMKUP,"Text"];
Run[LaTeXToPDF<>" CP"<>FLNM3];
Run[BibTeX<>" CP"<>StringReplace[FLNM3,".tex"->""]];
Run[LaTeXToPDF<>" CP"<>FLNM3];
Run[LaTeXToPDF<>" CP"<>FLNM3];

];


(* EXPORT ALL MATHEMATICA CODE *)

Print["EXPORTING MATHEMATICA CODE TO TXT"];

Export["MCode"<>StringReplace[FLNM,".tex"->".txt"],
StringJoin@@Join[
{"(********************\n\n Preamble\n\n********************)\n\n "},Riffle[PRE,"\n\n (******)\n\n"],
{"(********************\n\n Auxiliary Results\n\n********************)\n\n "},Riffle[ART,"\n\n (******)\n\n"],
{"(********************\n\n Formulas\n\n********************)\n\n "},Riffle[FRM,"\n\n (******)\n\n"],
Riffle[FRMS,"\n\n (******)\n\n"], Riffle[FRMP,"\n\n (******)\n\n"],
{"\n\n(********************\n\n Images\n\n********************)\n\n"}, Riffle[IMG,"\n\n (******)\n\n"],
{"\n\n(********************\n\n Movies\n\n********************)\n\n"}, Riffle[MOV,"\n\n (******)\n\n"],
{"\n\n(********************\n\n Tables \n\n********************)\n\n"}, Riffle[TBL,"\n\n (******)\n\n"],
{"\n\n(********************\n\n Listing \n\n********************)\n\n"}, Riffle[LST,"\n\n (******)\n\n"],
{"\n\n(********************\n\n Executables \n\n********************)\n\n"}, Riffle[EXE,"\n\n (******)\n\n"],
{"\n\n(********************\n\n PExecutables \n\n********************)\n\n"}, Riffle[PEX,"\n\n (******)\n\n"]
]];


(* HTML GENERATOR *)

If[html,

(*CREATE TEMPORARY DIRECTORY need to move this somewhere because of the mathematica export directory *)

	CreateDirectory["tmp"] //Quiet;
	SetDirectory[DirectoryName[file]<>"/tmp"]//Quiet;


(*EXPORT NO FORMULAS VERSION AND COMPILE IT IN PDF AND IN HTML*)


Print["PDF - NO FORMULAS - GC"<>FLNM3];
Print["HTML - NO FORMULAS - GC"<>FLNM3];

Export["GC"<>FLNM3,TXTNoformulas,"Text"];
Run[LaTeXToPDF<>" GC"<>FLNM3];
Run["PATH="<>LaTeXDir<>":$PATH; "<>HTLaTeX<>" GC"<>FLNM3];

(* READS HTML AND EXPORTS A TXT VERSION *)


NEWTXT=StringReplace[Import[StringReplace["GC"<>FLNM3, ".tex"->".html"]],{"\r\n"->"","\n"->"", (Whitespace)->" "}];



Export[StringReplace["GC"<>FLNM3,".tex"->".txt"], NEWTXT,"Text"];

SetDirectory[DirectoryName[file]]//Quiet;

]

(* TEXT ANALYSIS - ONLY POSSIBLE IF html OPTION IS ON *)


If[html&&texta, 

ANTTXT=GenAnnLaTeX[ProcessText[NEWTXT]];

SetDirectory[DirectoryName[file]<>"/tmp"]//Quiet;
Export["ANT"<>FLNM3 ,"\\documentclass{amsart}\n\\usepackage{color}\n\\begin{document}\n"<>BasicTextStatisticsTex[NEWTXT]<>"\\section{Sentence Analysis}"
<>StringReplace[ANTTXT,"."->".\n\n\\noindent "]<>"\\end{document}", "Text"];
Run[LaTeXToPDF<>" ANT"<>FLNM3];



];

(* FINAL CLEAN-UP *)

Print["Final clean-up - the files CL*.* and CP*.* are moved to the temporary directory.
To compile them move them back to the ORIGINAL directory"]; 

(* next line is to escape spaces in directory names *)

(*
DIRNAME2=StringReplace[DirectoryName[file]," "->"\\ "];
*)

DIRNAME2="\""~~DirectoryName[file]~~"\"";

(*
Print[file];
Print[DirectoryName[file]];
Print[DIRNAME2];
Print[FLNM3];
*)


SetDirectory[DirectoryName[file]]//Quiet;
Run["mv "~~DIRNAME2~~"CL"<>StringReplace[FLNM3, ".tex"->""]<>".* "~~DIRNAME2~~"tmp/"];
(*Print["mv "~~DIRNAME2~~"CL"<>StringReplace[FLNM3, ".tex"->""]<>".* "~~DIRNAME2~~"tmp/"];*)
Run["mv "~~DIRNAME2~~"CP"<>StringReplace[FLNM3, ".tex"->""]<>".* "~~DIRNAME2~~"tmp/"];
(*Print["mv "~~DIRNAME2~~"CP"<>StringReplace[FLNM3, ".tex"->""]<>".* "~~DIRNAME2~~"tmp/"];*)
Run["mv "~~DIRNAME2~~"FC"<>StringReplace[FLNM3, ".tex"->""]<>".* "~~DIRNAME2~~"tmp/"];

CreateDirectory["MLaTeX"] //Quiet;
(*
Print["mv "~~DIRNAME2~~"CL"<>StringReplace[FLNM3, ".tex"->""]<>".* "~~DIRNAME2~~"tmp/"];
Print["cp "~~DIRNAME2~~"tmp/FC"<>StringReplace[FLNM3, ".tex"->".pdf"]<>" "~~DIRNAME2~~"MLaTeX/"];
Print["cp "~~DIRNAME2~~"tmp/ANT"<>StringReplace[FLNM3, ".tex"->".pdf"]<>" "~~DIRNAME2~~"MLaTeX/"];
*)

Run["cp "~~DIRNAME2~~"tmp/CL"<>StringReplace[FLNM3, ".tex"->".pdf"]<>" "~~DIRNAME2~~"MLaTeX/"];
Run["cp "~~DIRNAME2~~"tmp/CL"<>FLNM3<>" "~~DIRNAME2~~"MLaTeX/"];
Run["cp "~~DIRNAME2~~"tmp/FC"<>StringReplace[FLNM3, ".tex"->".pdf"]<>" "~~DIRNAME2~~"MLaTeX/"];
Run["cp "~~DIRNAME2~~"tmp/CP"<>StringReplace[FLNM3, ".tex"->".pdf"]~~" "~~DIRNAME2~~"MLaTeX/"];
Run["cp "~~DIRNAME2~~"tmp/ANT"<>StringReplace[FLNM3, ".tex"->".pdf"]<>" "~~DIRNAME2~~"MLaTeX/"];
Run["cp "~~DIRNAME2~~"tmp/GC"<>StringReplace[FLNM3, ".tex"->".html"]<>" "~~DIRNAME2~~"MLaTeX/"];
Run["cp "~~DIRNAME2~~"tmp/MCODE"<>StringReplace[FLNM3, ".tex"->".txt"]<>" "~~DIRNAME2~~"MLaTeX/"];

]






End[]


EndPackage[]



