//#Safe
/*
 * This example shows how the join statement handles multiple return values.
 *
 * Author: Lars Nitzke (lars.nitzke@outlook.com)
 * Date: 22.08.2018
 * 
 */

procedure ULTIMATE.start();

implementation ULTIMATE.start()
{
    var x : int;
    var y : bool;
    x := 1;

    fork x foo(x);
    
    x := 3;
    
    join 1 assign x, y;
    assert (x == 1 && !y);
}

procedure foo(num : int) returns(ret : int, ret_bool : bool);

implementation foo(num : int) returns(ret : int, ret_bool : bool)
{
    if (num  < 10) {
        ret := num;
        ret_bool := false;
    } else {
        ret := 9;
        ret_bool := true;
    }
}
