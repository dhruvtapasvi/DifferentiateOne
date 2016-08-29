datatype expr = sum of expr * expr
            |   prod of expr * expr
            |   recip of expr
            |   const of int
            |   x
            |   intpower of int*expr
            |   exp of expr
            |   sin of expr
            |   cos of expr
            |   log of expr
            |   tan of expr
            |   cosec of expr
            |   sec of expr
            |   cot of expr
            |   sinh of expr
            |   cosh of expr;

fun simplify (sum(a,b)) =
        let val a' = simplify(a)
            val b' = simplify(b)
        in if (a' = const(0)) then b'
           else if (b' = const(0)) then a'
           else sum(a',b')
        end
|   simplify (prod(a,b)) =
        let val a' = simplify a
            val b' = simplify b
        in if (a' = const(0) orelse b' = const(0)) then const(0)
           else if (a' = const(1)) then b'
           else if (b' = const(1)) then a'
           else prod(a',b')
        end
|   simplify (intpower(0,_)) = const(1)
|   simplify (intpower(1,myfunc)) = simplify myfunc
|   simplify (intpower(a,myfunc)) = intpower(a,simplify myfunc)
|   simplify (sin(myfunc)) =
        (case (simplify myfunc) of (const(a)) => (if (a mod 180 = 0) then const(0) else sin(const(a)))
            |                     myfunc' => (sin(myfunc')))
|   simplify (cos(myfunc)) =
        (case (simplify myfunc) of (const(a)) => (if ((a mod 90 = 0) andalso not (a mod 180 = 0)) then const(0) else cos(const(a)))
            |                     myfunc' => (cos(myfunc')))
|   simplify (exp(myfunc)) = 
        (case (simplify myfunc) of (const(0)) => (const(1)) | myfunc' => (exp(myfunc')))
|   simplify (recip(func)) = recip(simplify func)
|   simplify (log(func)) = (case (simplify func) of const(1) => const(0) | myfunc' => log(myfunc'))
|   simplify (sinh(func)) = (case (simplify func) of const(0) => const(0) | myfunc' => sinh(myfunc'))
|   simplify (cosh(func)) = (case(simplify func) of const(0) => const(1) | myfunc' => cosh(myfunc'))
|   simplify myExpr = myExpr;

fun diff (sum(z,y)) = sum(diff z, diff y)
|   diff (prod(z,y)) = sum(prod(diff z, y),prod(z,diff y))
|   diff (const(_)) = const(0)
|   diff x = const(1)
|   diff (intpower(a,func)) = prod(const(a),prod(diff func,intpower(a-1,func)))
|   diff (exp(func)) = prod(diff func,exp(func))
|   diff (sin(func)) = prod(diff func, cos(func))
|   diff (cos(func)) = prod(const(~1), prod(diff func, sin(func)))
|   diff (recip(func)) = prod(const(~1),prod(diff func,recip(intpower(2,func))))
|   diff (log(func)) = prod(diff func,recip(func))
|   diff (tan(func)) = prod(diff func,intpower(2,sec(func)))
|   diff (cosec(func)) = prod(diff func, prod(const(~1),prod(cot(func),cosec(func))))
|   diff (sec(func)) = prod(func,prod(tan(func),sec(func)))
|   diff (cot(func)) = prod(const(~1),intpower(2,cosec(func)))
|   diff (sinh(func)) = prod(diff func,cosh(func))
|   diff (cosh(func)) = prod(diff func,sinh(func));

fun diffans myfunc = simplify(diff(myfunc));
    
fun pri (sum(z,y)) = (pri z) ^ " + " ^ (pri y)
|   pri (prod(z,y)) = (pri z) ^ " * " ^ (pri y)
|   pri (const(a)) = Int.toString(a)
|   pri x = "x"
|   pri (intpower(a,func)) = "(" ^ (pri func) ^ ") ^ " ^ (Int.toString(a))
|   pri (exp(func)) = "exp(" ^ (pri func) ^ ")"
|   pri (sin(func)) = "sin(" ^ (pri func) ^ ")"
|   pri (cos(func)) = "cos(" ^ (pri func) ^ ")"
|   pri (log(func)) = "log(" ^ (pri func) ^ ")"
|   pri (recip(func)) = "1 / (" ^ (pri func) ^ ")"
|   pri (tan(func)) = "tan(" ^ (pri func) ^ ")"
|   pri (cosec(func)) = "cosec(" ^ (pri func) ^ ")"
|   pri (sec(func)) = "sec(" ^ (pri func) ^ ")"
|   pri (cot(func)) = "cot(" ^ (pri func) ^ ")"
|   pri (sinh(func)) = "sinh(" ^ (pri func) ^ ")"
|   pri (cosh(func)) = "cosh(" ^ (pri func) ^ ")";

fun eval(p :real, sum(a,b)) = eval(p,a) + eval(p,b)
|   eval(p,prod(a,b)) = eval(p,a)*eval(p,b)
|   eval(p,recip(a)) = 1.0/(eval(p,a))
|   eval(p,const(a)) = Real.fromInt(a)
|   eval(p,x) = p
|   eval(p,intpower(a,func)) = Math.pow(eval(p,func),Real.fromInt(a))
|   eval(p,exp(myfunc)) = Math.exp(eval(p,myfunc))
|   eval(p,sin(myfunc)) = Math.sin(eval(p,myfunc))
|   eval(p,cos(myfunc)) = Math.cos(eval(p,myfunc))
|   eval(p,tan(myfunc)) = Math.tan(eval(p,myfunc))
|   eval(p,sec(myfunc)) = 1.0/Math.cos(eval(p,myfunc))
|   eval(p,cosec(myfunc)) = 1.0/Math.sin(eval(p,myfunc))
|   eval(p,cot(myfunc)) = 1.0/Math.tan(eval(p,myfunc))
|   eval(p,log(myfunc)) = Math.ln(eval(p,myfunc))
|   eval(p,sinh(myfunc)) = Math.sinh(eval(p,myfunc))
|   eval(p,cosh(myfunc)) = Math.cosh(eval(p,myfunc));

fun manyderivate n func = 
    if (n=0) then func
    else manyderivate (n-1) (diffans func);

fun diffpri func = pri(diffans func);

fun derivative func p = eval(p,diffans(func));

(* Baba *)
val baba1 = sum(intpower(2,x),const(~2));
pri baba1;
val baba1' = diff baba1;
pri baba1';