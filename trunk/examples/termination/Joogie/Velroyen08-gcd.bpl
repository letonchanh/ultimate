type ref;
type realVar;
type classConst;
// type Field x;
// var $HeapVar : <x>[ref, Field x]x;

const unique $null : ref ;
const unique $intArrNull : [int]int ;
const unique $realArrNull : [int]realVar ;
const unique $refArrNull : [int]ref ;

const unique $arrSizeIdx : int;
var $intArrSize : [int]int;
var $realArrSize : [realVar]int;
var $refArrSize : [ref]int;

var $stringSize : [ref]int;

//built-in axioms 
axiom ($arrSizeIdx == -1);

//note: new version doesn't put helpers in the perlude anymore//Prelude finished 





// procedure is generated by joogie.
function {:inline true} $neref(x : ref, y : ref) returns (__ret : int) {
if (x != y) then 1 else 0
}


// procedure is generated by joogie.
function {:inline true} $realarrtoref($param00 : [int]realVar) returns (__ret : ref);



// procedure is generated by joogie.
function {:inline true} $modreal($param00 : realVar, $param11 : realVar) returns (__ret : realVar);



// procedure is generated by joogie.
function {:inline true} $leref($param00 : ref, $param11 : ref) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $modint($param00 : int, $param11 : int) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $gtref($param00 : ref, $param11 : ref) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $eqrealarray($param00 : [int]realVar, $param11 : [int]realVar) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $addint(x : int, y : int) returns (__ret : int) {
(x + y)
}


// procedure is generated by joogie.
function {:inline true} $subref($param00 : ref, $param11 : ref) returns (__ret : ref);



// procedure is generated by joogie.
function {:inline true} $inttoreal($param00 : int) returns (__ret : realVar);



// procedure is generated by joogie.
function {:inline true} $shrint($param00 : int, $param11 : int) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $negReal($param00 : realVar) returns (__ret : int);



	 //  @line: 2
// <simple.gcd.Gcd: void <init>()>
procedure void$simple.gcd.Gcd$$la$init$ra$$2228(__this : ref)  requires ($neref((__this), ($null))==1);
 {
var r01 : ref;
Block16:
	r01 := __this;
	 assert ($neref((r01), ($null))==1);
	 //  @line: 3
	 call void$java.lang.Object$$la$init$ra$$28((r01));
	 return;
}


// procedure is generated by joogie.
function {:inline true} $ushrint($param00 : int, $param11 : int) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $refarrtoref($param00 : [int]ref) returns (__ret : ref);



// procedure is generated by joogie.
function {:inline true} $divref($param00 : ref, $param11 : ref) returns (__ret : ref);



// procedure is generated by joogie.
function {:inline true} $mulref($param00 : ref, $param11 : ref) returns (__ret : ref);



// procedure is generated by joogie.
function {:inline true} $neint(x : int, y : int) returns (__ret : int) {
if (x != y) then 1 else 0
}


// procedure is generated by joogie.
function {:inline true} $ltreal($param00 : realVar, $param11 : realVar) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $reftorefarr($param00 : ref) returns (__ret : [int]ref);



// procedure is generated by joogie.
function {:inline true} $gtint(x : int, y : int) returns (__ret : int) {
if (x > y) then 1 else 0
}


// procedure is generated by joogie.
function {:inline true} $reftoint($param00 : ref) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $addref($param00 : ref, $param11 : ref) returns (__ret : ref);



// procedure is generated by joogie.
function {:inline true} $xorreal($param00 : realVar, $param11 : realVar) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $andref($param00 : ref, $param11 : ref) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $cmpreal(x : realVar, y : realVar) returns (__ret : int) {
if ($ltreal((x), (y)) == 1) then 1 else if ($eqreal((x), (y)) == 1) then 0 else -1
}


// procedure is generated by joogie.
function {:inline true} $addreal($param00 : realVar, $param11 : realVar) returns (__ret : realVar);



// procedure is generated by joogie.
function {:inline true} $gtreal($param00 : realVar, $param11 : realVar) returns (__ret : int);



// <java.lang.Object: void <init>()>
procedure void$java.lang.Object$$la$init$ra$$28(__this : ref);



// procedure is generated by joogie.
function {:inline true} $eqreal(x : realVar, y : realVar) returns (__ret : int) {
if (x == y) then 1 else 0
}


// procedure is generated by joogie.
function {:inline true} $ltint(x : int, y : int) returns (__ret : int) {
if (x < y) then 1 else 0
}


// procedure is generated by joogie.
function {:inline true} $newvariable($param00 : int) returns (__ret : ref);



// procedure is generated by joogie.
function {:inline true} $divint($param00 : int, $param11 : int) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $geint(x : int, y : int) returns (__ret : int) {
if (x >= y) then 1 else 0
}


// procedure is generated by joogie.
function {:inline true} $mulint($param00 : int, $param11 : int) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $leint(x : int, y : int) returns (__ret : int) {
if (x <= y) then 1 else 0
}


// procedure is generated by joogie.
function {:inline true} $shlref($param00 : ref, $param11 : ref) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $eqrefarray($param00 : [int]ref, $param11 : [int]ref) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $reftointarr($param00 : ref) returns (__ret : [int]int);



// procedure is generated by joogie.
function {:inline true} $ltref($param00 : ref, $param11 : ref) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $mulreal($param00 : realVar, $param11 : realVar) returns (__ret : realVar);



// procedure is generated by joogie.
function {:inline true} $shrref($param00 : ref, $param11 : ref) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $ushrreal($param00 : realVar, $param11 : realVar) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $shrreal($param00 : realVar, $param11 : realVar) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $divreal($param00 : realVar, $param11 : realVar) returns (__ret : realVar);



// procedure is generated by joogie.
function {:inline true} $orint($param00 : int, $param11 : int) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $reftorealarr($param00 : ref) returns (__ret : [int]realVar);



// procedure is generated by joogie.
function {:inline true} $cmpref(x : ref, y : ref) returns (__ret : int) {
if ($ltref((x), (y)) == 1) then 1 else if ($eqref((x), (y)) == 1) then 0 else -1
}


	 //  @line: 9
// <simple.gcd.Main: void main(java.lang.String[])>
procedure void$simple.gcd.Main$main$2231($param_0 : [int]ref)
  modifies $stringSize;
 {
var $r421 : ref;
var $i222 : int;
var i626 : int;
var $i019 : int;
var $i323 : int;
var $i120 : int;
var i525 : int;
var $r318 : ref;
var $r112 : ref;
var $r215 : ref;
var r011 : [int]ref;

 //temp local variables 
var $freshlocal0 : int;

Block26:
	r011 := $param_0;
	 assert ($geint((2), (0))==1);
	 assert ($ltint((2), ($refArrSize[r011[$arrSizeIdx]]))==1);
	 //  @line: 10
	$r112 := r011[2];
	i525 := $stringSize[$r112];
	 assert ($geint((3), (0))==1);
	 assert ($ltint((3), ($refArrSize[r011[$arrSizeIdx]]))==1);
	 //  @line: 11
	$r215 := r011[3];
	i626 := $stringSize[$r215];
	 assert ($geint((0), (0))==1);
	 assert ($ltint((0), ($refArrSize[r011[$arrSizeIdx]]))==1);
	 //  @line: 12
	$r318 := r011[0];
	$i019 := $stringSize[$r318];
	 //  @line: 12
	$i120 := $modint(($i019), (2));
	 goto Block27;
	 //  @line: 12
Block27:
	 goto Block30, Block28;
	 //  @line: 12
Block30:
	 //  @line: 12
	 assume ($negInt(($neint(($i120), (0))))==1);
	 //  @line: 13
	i525 := $negInt((i525));
	 goto Block29;
	 //  @line: 12
Block28:
	 assume ($neint(($i120), (0))==1);
	 goto Block29;
	 //  @line: 15
Block29:
	 assert ($geint((1), (0))==1);
	 assert ($ltint((1), ($refArrSize[r011[$arrSizeIdx]]))==1);
	 //  @line: 15
	$r421 := r011[1];
	$i222 := $stringSize[$r421];
	 //  @line: 15
	$i323 := $modint(($i222), (2));
	 goto Block31;
	 //  @line: 15
Block31:
	 goto Block34, Block32;
	 //  @line: 15
Block34:
	 //  @line: 15
	 assume ($negInt(($neint(($i323), (0))))==1);
	 //  @line: 16
	i626 := $negInt((i626));
	 goto Block33;
	 //  @line: 15
Block32:
	 assume ($neint(($i323), (0))==1);
	 goto Block33;
	 //  @line: 18
Block33:
	 //  @line: 18
	 call $freshlocal0 := int$simple.gcd.Gcd$gcd$2229((i525), (i626));
	 return;
}


// procedure is generated by joogie.
function {:inline true} $realtoint($param00 : realVar) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $geref($param00 : ref, $param11 : ref) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $orreal($param00 : realVar, $param11 : realVar) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $eqint(x : int, y : int) returns (__ret : int) {
if (x == y) then 1 else 0
}


// procedure is generated by joogie.
function {:inline true} $ushrref($param00 : ref, $param11 : ref) returns (__ret : int);



	 //  @line: 33
// <simple.gcd.Gcd: int gcd(int,int)>
procedure int$simple.gcd.Gcd$gcd$2229($param_0 : int, $param_1 : int) returns (__ret : int) {
var i16 : int;
var i28 : int;
var i39 : int;
var i05 : int;
Block17:
	i05 := $param_0;
	i16 := $param_1;
	 goto Block18;
	 //  @line: 37
Block18:
	 goto Block19, Block21;
	 //  @line: 37
Block19:
	 assume ($leint((i16), (i05))==1);
	 goto Block20;
	 //  @line: 37
Block21:
	 //  @line: 37
	 assume ($negInt(($leint((i16), (i05))))==1);
	 //  @line: 38
	i28 := i05;
	 //  @line: 39
	i05 := i16;
	 //  @line: 40
	i16 := i28;
	 goto Block20;
	 //  @line: 43
Block20:
	 goto Block24, Block22;
	 //  @line: 43
Block24:
	 //  @line: 43
	 assume ($negInt(($eqint((i16), (0))))==1);
	 //  @line: 44
	i39 := $subint((i05), (i16));
	 //  @line: 45
	i05 := i16;
	 //  @line: 46
	i16 := i39;
	 goto Block20;
	 //  @line: 43
Block22:
	 assume ($eqint((i16), (0))==1);
	 goto Block23;
	 //  @line: 48
Block23:
	 //  @line: 48
	__ret := i05;
	 return;
}


// procedure is generated by joogie.
function {:inline true} $modref($param00 : ref, $param11 : ref) returns (__ret : ref);



// procedure is generated by joogie.
function {:inline true} $eqintarray($param00 : [int]int, $param11 : [int]int) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $negRef($param00 : ref) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $lereal($param00 : realVar, $param11 : realVar) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $nereal(x : realVar, y : realVar) returns (__ret : int) {
if (x != y) then 1 else 0
}


	 //  @line: 3
// <simple.gcd.Main: void <init>()>
procedure void$simple.gcd.Main$$la$init$ra$$2230(__this : ref)  requires ($neref((__this), ($null))==1);
 {
var r010 : ref;
Block25:
	r010 := __this;
	 assert ($neref((r010), ($null))==1);
	 //  @line: 4
	 call void$java.lang.Object$$la$init$ra$$28((r010));
	 return;
}


// procedure is generated by joogie.
function {:inline true} $instanceof($param00 : ref, $param11 : classConst) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $xorref($param00 : ref, $param11 : ref) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $orref($param00 : ref, $param11 : ref) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $intarrtoref($param00 : [int]int) returns (__ret : ref);



// procedure is generated by joogie.
function {:inline true} $subreal($param00 : realVar, $param11 : realVar) returns (__ret : realVar);



// procedure is generated by joogie.
function {:inline true} $shlreal($param00 : realVar, $param11 : realVar) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $negInt(x : int) returns (__ret : int) {
if (x == 0) then 1 else 0
}


// <java.lang.String: int length()>
procedure int$java.lang.String$length$59(__this : ref) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $gereal($param00 : realVar, $param11 : realVar) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $eqref(x : ref, y : ref) returns (__ret : int) {
if (x == y) then 1 else 0
}


// procedure is generated by joogie.
function {:inline true} $cmpint(x : int, y : int) returns (__ret : int) {
if (x < y) then 1 else if (x == y) then 0 else -1
}


// procedure is generated by joogie.
function {:inline true} $andint($param00 : int, $param11 : int) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $andreal($param00 : realVar, $param11 : realVar) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $shlint($param00 : int, $param11 : int) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $xorint($param00 : int, $param11 : int) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $subint(x : int, y : int) returns (__ret : int) {
(x - y)
}


