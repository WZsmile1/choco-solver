/**
 * Copyright (c) 2015, Ecole des Mines de Nantes
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. All advertising materials mentioning features or use of this software
 *    must display the following acknowledgement:
 *    This product includes software developed by the <organization>.
 * 4. Neither the name of the <organization> nor the
 *    names of its contributors may be used to endorse or promote products
 *    derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY <COPYRIGHT HOLDER> ''AS IS'' AND ANY
 * EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL <COPYRIGHT HOLDER> BE LIABLE FOR ANY
 * DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
package org.chocosolver.solver.variables;

import org.chocosolver.solver.Cause;
import org.chocosolver.solver.Solver;
import org.chocosolver.solver.constraints.Constraint;
import org.chocosolver.solver.constraints.Operator;
import org.chocosolver.solver.constraints.nary.sum.PropScalar;
import org.chocosolver.solver.constraints.ternary.Max;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.search.strategy.ISF;
import org.chocosolver.solver.search.strategy.IntStrategyFactory;
import org.chocosolver.solver.search.strategy.SetStrategyFactory;
import org.testng.Assert;
import org.testng.annotations.Test;

/**
 * <br/>
 *
 * @author Charles Prud'homme
 * @since 25/08/11
 */
public class ViewsTest {

    public static void check(Solver ref, Solver solver, long seed, boolean strict, boolean solveAll) {
//        SearchMonitorFactory.log(ref, true, true);
//        SearchMonitorFactory.log(solver, true, true);
        if (solveAll) {
            ref.findAllSolutions();
            solver.findAllSolutions();
        } else {
//            System.out.printf("%s\n", ref.toString());
            ref.findSolution();
//            System.out.printf("%s\n", solver.toString());
            solver.findSolution();
        }
        Assert.assertEquals(solver.getMeasures().getSolutionCount(),
                ref.getMeasures().getSolutionCount(), "solutions (" + seed + ")");
//        System.out.printf("%d : %d vs. %d  -- ", seed, ref.getMeasures().getNodeCount(),
//                solver.getMeasures().getNodeCount());
        if (strict) {
            Assert.assertEquals(solver.getMeasures().getNodeCount(), ref.getMeasures().getNodeCount(), "nodes (" + seed + ")");
        } else {
            Assert.assertTrue(ref.getMeasures().getNodeCount() >=
                    solver.getMeasures().getNodeCount(), seed + "");
        }
//        System.out.printf("%d : %d vs. %d (%f)\n", seed, ref.getMeasures().getTimeCount(),
//                solver.getMeasures().getTimeCount(),
//                ref.getMeasures().getTimeCount() / (float) solver.getMeasures().getTimeCount());
    }


    @Test(groups="10s", timeOut=60000)
    public void test1() {
        // Z = X + Y
//        int seed = 5;
        for (int seed = 0; seed < 9999; seed++) {
            Solver ref = new Solver();
            Solver solver = new Solver();
            {
                IntVar x = ref.intVar("x", 0, 2, false);
                IntVar y = ref.intVar("y", 0, 2, false);
                IntVar z = ref.intVar("z", 0, 4, false);
                ref.post(new Constraint("SP", new PropScalar(new IntVar[]{x, y, z}, new int[]{1, 1, -1}, 2, Operator.EQ, 0)));
                ref.set(IntStrategyFactory.random_value(new IntVar[]{x, y, z}, seed));

            }
            {
                IntVar x = solver.intVar("x", 0, 2, false);
                IntVar y = solver.intVar("y", 0, 2, false);
                IntVar z = solver.intVar("Z", 0, 200, false);
                solver.post(solver.sum(new IntVar[]{x, y}, "=", z));
                solver.set(IntStrategyFactory.random_value(new IntVar[]{x, y, z}, seed));

            }
            check(ref, solver, seed, false, true);
        }
    }

    @Test(groups="10s", timeOut=60000)
    public void test1a() {
        // Z = X + Y (bounded)
        for (int seed = 0; seed < 9999; seed++) {
            Solver ref = new Solver();
            Solver solver = new Solver();
            {
                IntVar x = ref.intVar("x", 0, 2, true);
                IntVar y = ref.intVar("y", 0, 2, true);
                IntVar z = ref.intVar("z", 0, 4, true);
                ref.post(new Constraint("SP", new PropScalar(new IntVar[]{x, y, z}, new int[]{1, 1, -1}, 2, Operator.EQ, 0)));
                ref.set(IntStrategyFactory.random_bound(new IntVar[]{x, y, z}, seed));

            }
            {
                IntVar x = solver.intVar("x", 0, 2, true);
                IntVar y = solver.intVar("y", 0, 2, true);
                IntVar z = solver.intVar("Z", 0, 200, false);
                solver.post(solver.sum(new IntVar[]{x, y}, "=", z));
                solver.set(IntStrategyFactory.random_bound(new IntVar[]{x, y, z}, seed));

            }
            check(ref, solver, seed, true, true);
        }
    }

    @Test(groups="10s", timeOut=60000)
    public void testa() {
        // Z = max(X + Y)
        for (int seed = 0; seed < 9999; seed += 1) {
            Solver ref = new Solver();
            Solver solver = new Solver();
            {
                IntVar x = ref.intVar("x", 0, 2, false);
                IntVar y = ref.intVar("y", 0, 2, false);
                IntVar z = ref.intVar("z", 0, 2, true);
                ref.post(ref.max(z, x, y));
                ref.set(IntStrategyFactory.random_bound(new IntVar[]{x, y, z}, seed));

            }
            {
                IntVar x = solver.intVar("x", 0, 2, false);
                IntVar y = solver.intVar("y", 0, 2, false);
                IntVar z = Max.var(x, y);
                solver.set(IntStrategyFactory.random_bound(new IntVar[]{x, y, z}, seed));

            }
            check(ref, solver, seed, false, true);
        }
    }

    @Test(groups="10s", timeOut=60000)
    public void test1b() {
        // Z = |X|
        for (int seed = 0; seed < 9999; seed++) {
            Solver ref = new Solver();
            Solver solver = new Solver();
            {
                IntVar x = ref.intVar("x", -2, 2, false);
                IntVar z = ref.intVar("z", 0, 2, false);

                ref.post(ref.absolute(z, x));
                ref.set(IntStrategyFactory.random_value(new IntVar[]{x, z}, seed));
            }
            {
                IntVar x = solver.intVar("x", -2, 2, false);
                IntVar z = solver.intAbsView(x);
                solver.set(IntStrategyFactory.random_bound(new IntVar[]{x, z}, seed));

            }
            check(ref, solver, seed, true, true);
        }
    }

    @Test(groups="10s", timeOut=60000)
    public void test1bb() {
        // Z = X + c
        for (int seed = 0; seed < 9999; seed++) {
            Solver ref = new Solver();
            Solver solver = new Solver();
            {
                IntVar x = ref.intVar("x", -2, 2, false);
                IntVar z = ref.intVar("z", -1, 3, false);

                ref.post(ref.arithm(z, "=", x, "+", 1));
                ref.set(IntStrategyFactory.random_value(new IntVar[]{x, z}, seed));
            }
            {
                IntVar x = solver.intVar("x", -2, 2, false);
                IntVar z = solver.intOffsetView(x, 1);
                solver.set(IntStrategyFactory.random_value(new IntVar[]{x, z}, seed));

            }
            check(ref, solver, seed, true, true);
        }
    }

    @Test(groups="10s", timeOut=60000)
    public void test1bbb() {
        // Z = X * c
        for (int seed = 0; seed < 9999; seed++) {
            Solver ref = new Solver();
            Solver solver = new Solver();
            {
                IntVar x = ref.intVar("x", -2, 2, false);
                IntVar z = ref.intVar("z", -4, 4, false);

                ref.post(ref.times(x, ref.intVar(2), z));
                ref.set(IntStrategyFactory.random_value(new IntVar[]{x, z}, seed));
            }
            {
                IntVar x = solver.intVar("x", -2, 2, false);
                IntVar z = solver.intScaleView(x, 2);
                solver.set(IntStrategyFactory.random_value(new IntVar[]{x, z}, seed));

            }
            check(ref, solver, seed, false, true);
        }
    }

    @Test(groups="10s", timeOut=60000)
    public void test1c() {
        // Z = -X
        for (int seed = 0; seed < 9999; seed++) {
            Solver ref = new Solver();
            Solver solver = new Solver();
            {
                IntVar x = ref.intVar("x", 0, 2, false);
                IntVar z = ref.intVar("z", -2, 0, false);

                ref.post(ref.arithm(z, "+", x, "=", 0));
                ref.set(IntStrategyFactory.random_value(new IntVar[]{x, z}, seed));
            }
            {
                IntVar x = solver.intVar("x", 0, 2, false);
                IntVar z = solver.intMinusView(x);
                solver.set(IntStrategyFactory.random_value(new IntVar[]{x, z}, seed));

            }
            check(ref, solver, seed, true, true);
        }
    }

    @Test(groups="5m", timeOut=300000)
    public void test1d() {
        // Z = X + Y + ...
        for (int seed = 2; seed < 9; seed += 1) {
            Solver ref = new Solver();
            Solver solver = new Solver();
            int n = seed * 2;
            {
                IntVar[] x = ref.intVarArray("x", n, 0, 2, false);
                ref.post(ref.sum(x, "=", n));
                ref.set(IntStrategyFactory.minDom_LB(x));
            }
            {
                IntVar[] x = solver.intVarArray("x", n, 0, 2, false);
                IntVar[] y = new IntVar[seed];
                for (int i = 0; i < seed; i++) {
                    y[i] = solver.intVar("Z", 0, 200, false);
                    solver.post(solver.sum(new IntVar[]{x[i], x[i + seed]}, "=", y[i]));
                }
                solver.post(solver.sum(y, "=", n));

                solver.set(IntStrategyFactory.minDom_LB(x));

            }
            check(ref, solver, seed, true, true);
        }
    }


    @Test(groups="1s", timeOut=60000)
    public void test1f() {
        // Z = MAX(X,Y)
        Solver ref = new Solver();
        Solver solver = new Solver();
        {
            IntVar x = ref.intVar("x", 160, 187, false);
            IntVar y = ref.intVar("y", -999, 999, false);
            IntVar z = ref.intVar("z", -9999, 9999, false);
            ref.post(ref.arithm(z, "+", x, "=", 180));
            ref.post(ref.max(y, ref.intVar(0), z));
        }
        {
            IntVar x = solver.intVar("x", 160, 187, false);
            IntVar y = solver.intVar("y", -999, 999, false);
            IntVar z = solver.intOffsetView(solver.intMinusView(x), 180);
            solver.post(solver.max(y, solver.intVar(0), z));

            check(ref, solver, 0, false, true);
        }
    }


    @Test(groups="10s", timeOut=60000)
    public void test2() {
        // Z = X - Y
        for (int seed = 0; seed < 9999; seed++) {
            Solver ref = new Solver();
            Solver solver = new Solver();
            {
                IntVar x = ref.intVar("x", 0, 2, false);
                IntVar y = ref.intVar("y", 0, 2, false);
                IntVar z = ref.intVar("z", -2, 2, false);
                ref.post(new Constraint("SP", new PropScalar(new IntVar[]{x, y, z}, new int[]{1, -1, -1}, 1, Operator.EQ, 0)));
//				System.out.println(cstr);
                ref.set(IntStrategyFactory.random_value(new IntVar[]{x, y, z}, seed));

            }
            {
                IntVar x = solver.intVar("x", 0, 2, false);
                IntVar y = solver.intVar("y", 0, 2, false);
                IntVar z = solver.intVar("Z", -200, 200, false);
                Constraint cstr = solver.sum(new IntVar[]{z, y}, "=", x);
                solver.post(cstr);
//				System.out.println(cstr);
                solver.set(IntStrategyFactory.random_value(new IntVar[]{x, y, z}, seed));

            }
            check(ref, solver, seed, false, true);
        }
    }

    @Test(groups="10s", timeOut=60000)
    public void test3() {
        // Z = |X - Y|
        for (int seed = 0; seed < 9999; seed++) {
            Solver ref = new Solver();
            Solver solver = new Solver();
            {
                IntVar x = ref.intVar("x", 0, 2, false);
                IntVar y = ref.intVar("y", 0, 2, false);
                IntVar z = ref.intVar("z", -2, 2, false);
                IntVar az = ref.intVar("az", 0, 2, false);
                ref.post(new Constraint("SP", new PropScalar(new IntVar[]{x, y, z}, new int[]{1, -1, -1}, 1, Operator.EQ, 0)));
                ref.post(ref.absolute(az, z));
                ref.set(IntStrategyFactory.random_bound(new IntVar[]{x, y, az}, seed));
            }
            {
                IntVar x = solver.intVar("x", 0, 2, false);
                IntVar y = solver.intVar("y", 0, 2, false);
                IntVar z = solver.intVar("Z", -2, 2, false);
                IntVar az = solver.intAbsView(z);
                solver.post(solver.sum(new IntVar[]{z, y}, "=", x));
                solver.set(IntStrategyFactory.random_bound(new IntVar[]{x, y, az}, seed));
            }
            check(ref, solver, seed, true, true);
        }
    }

    @Test(groups="10s", timeOut=60000)
    public void test4() {
        // Z = |X - Y| + AllDiff
        for (int seed = 0; seed < 9999; seed++) {
            Solver ref = new Solver();
            Solver solver = new Solver();
            {
                IntVar x = ref.intVar("x", 0, 2, false);
                IntVar y = ref.intVar("y", 0, 2, false);
                IntVar z = ref.intVar("z", -2, 2, false);
                IntVar az = ref.intVar("az", 0, 2, false);
                ref.post(new Constraint("SP", new PropScalar(new IntVar[]{x, y, z}, new int[]{1, -1, -1}, 1, Operator.EQ, 0)));
                ref.post(ref.absolute(az, z));
                ref.post(ref.allDifferent(new IntVar[]{x, y, az}, "BC"));
                ref.set(IntStrategyFactory.random_bound(new IntVar[]{x, y, az}, seed));
            }
            {
                IntVar x = solver.intVar("x", 0, 2, false);
                IntVar y = solver.intVar("y", 0, 2, false);
                IntVar z = solver.intVar("z", -2, 2, false);
                solver.post(new Constraint("SP", new PropScalar(new IntVar[]{x, y, z}, new int[]{1, -1, -1}, 1, Operator.EQ, 0)));
                IntVar az = solver.intAbsView(z);
                solver.post(solver.allDifferent(new IntVar[]{x, y, az}, "BC"));
                solver.set(IntStrategyFactory.random_bound(new IntVar[]{x, y, az}, seed));
            }
            check(ref, solver, seed, true, true);
        }
    }

    @Test(groups="10s", timeOut=60000)
    public void test5() {
        // ~all-interval series
        int k = 5;
        for (int seed = 0; seed < 99; seed++) {
            Solver ref = new Solver();
            Solver solver = new Solver();
            {
                IntVar[] x = ref.intVarArray("x", k, 0, k - 1, false);
                IntVar[] y = ref.intVarArray("y", k - 1, -(k - 1), k - 1, false);
                IntVar[] t = ref.intVarArray("t", k - 1, 0, k - 1, false);
                for (int i = 0; i < k - 1; i++) {
                    ref.post(new Constraint("SP", new PropScalar(new IntVar[]{x[i + 1], x[i], y[i]}, new int[]{1, -1, -1}, 1, Operator.EQ, 0)));
                    ref.post(ref.absolute(t[i], y[i]));
                }
                ref.post(ref.allDifferent(x, "BC"));
                ref.post(ref.allDifferent(t, "BC"));
                ref.post(ref.arithm(x[1], ">", x[0]));
                ref.post(ref.arithm(t[0], ">", t[k - 2]));
                ref.set(IntStrategyFactory.random_value(x, seed));
            }
            {
                IntVar[] x = solver.intVarArray("x", k, 0, k - 1, false);
                IntVar[] t = new IntVar[k - 1];
                for (int i = 0; i < k - 1; i++) {
                    IntVar z = solver.intVar("Z", -200, 200, false);
                    solver.post(new Constraint("SP", new PropScalar(new IntVar[]{x[i + 1], x[i], z}, new int[]{1, -1, -1}, 1, Operator.EQ, 0)));
                    t[i] = solver.intAbsView(z);
                }
                solver.post(solver.allDifferent(x, "BC"));
                solver.post(solver.allDifferent(t, "BC"));
                solver.post(solver.arithm(x[1], ">", x[0]));
                solver.post(solver.arithm(t[0], ">", t[k - 2]));
                solver.set(IntStrategyFactory.random_value(x, seed));
            }
            check(ref, solver, k, true, true);
        }
    }


    @Test(groups="10s", timeOut=60000)
    public void test6() throws ContradictionException {
        Solver solver = new Solver();
        IntVar x = solver.intVar("x", 0, 10, false);
        IntVar y = solver.intAbsView(x);
        IntVar z = solver.intAbsView(solver.intAbsView(x));

        for (int j = 0; j < 200; j++) {
//            long t = -System.nanoTime();
            for (int i = 0; i < 999999; i++) {
                if (y.getLB() == x.getUB()) {
                    y.updateLowerBound(0, Cause.Null);
                }
            }
//            t += System.nanoTime();
//            System.out.printf("%.2fms vs. ", t / 1000 / 1000f);
//            t = -System.nanoTime();
            for (int i = 0; i < 999999; i++) {
                if (z.getLB() == x.getUB()) {
                    z.updateLowerBound(0, Cause.Null);
                }
            }
//            t += System.nanoTime();
//            System.out.printf("%.2fms\n", t / 1000 / 1000f);
        }
    }

    @Test(groups="1s", timeOut=60000)
    public void testJL1() throws ContradictionException {
        Solver s = new Solver();
        IntVar v1 = s.intVar("v1", -2, 2, false);
        IntVar v2 = s.intMinusView(s.intMinusView(s.intVar("v2", -2, 2, false)));
        s.post(s.arithm(v1, "=", v2));
        s.post(s.arithm(v2, "!=", 1));

        s.propagate();

        Assert.assertFalse(v1.contains(1));
    }

    @Test(groups="1s", timeOut=60000)
    public void testJL2() {
        Solver solver = new Solver();
        SetVar v1 = solver.setVar("{0,1}", new int[]{0, 1});
        SetVar v2 = solver.setVar("v2", new int[]{}, new int[]{0,1,2,3});
        solver.post(solver.subsetEq(new SetVar[]{v1, v2}));
        solver.set(SetStrategyFactory.force_first(new SetVar[]{v1, v2}));
        solver.findAllSolutions();
        Assert.assertEquals(solver.getMeasures().getSolutionCount(), 4);
    }

    @Test(groups="1s", timeOut=60000)
    public void testJL3() {
        Solver solver = new Solver();
        solver.post(solver.arithm(
                solver.intVar("int", -3, 3, false),
                "=",
                solver.intMinusView(solver.boolVar("bool"))));
        solver.findAllSolutions();
        Assert.assertEquals(solver.getMeasures().getSolutionCount(), 2);
    }

    @Test(groups="1s", timeOut=60000)
    public void testJL4() throws ContradictionException {
        Solver s = new Solver();
        BoolVar bool = s.boolVar("bool");
        BoolVar view = s.boolEqView(bool);
        SetVar set = s.setVar("set", new int[]{}, new int[]{0,1});
        s.post(s.setBoolsChanneling(new BoolVar[]{view, bool}, set, 0));
        s.post(s.member(s.ONE(), set));
        s.set(ISF.minDom_UB(bool));
        s.findAllSolutions();
        Assert.assertEquals(s.getMeasures().getSolutionCount(), 1);
    }

    @Test(groups="1s", timeOut=60000)
    public void testJG() throws ContradictionException {
        Solver s = new Solver();
        BoolVar bool = s.boolVar("bool");
        BoolVar view = s.boolEqView(bool);
        IntVar sum = s.intVar("sum", 0, 6, true);
        s.post(s.scalar(new IntVar[]{view, bool}, new int[]{1, 5}, "=", sum));
        s.post(s.arithm(sum, ">", 2));
        s.propagate();
        Assert.assertEquals(sum.isInstantiated(), true);
    }

    @Test(groups="1s", timeOut=60000)
    public void testJG2() throws ContradictionException {
        Solver s = new Solver();
        BoolVar bool = s.boolVar("bool");
        BoolVar view = s.boolNotView(bool);
        IntVar sum = s.intVar("sum", 0, 6, true);
        s.post(s.scalar(new IntVar[]{view, bool}, new int[]{1, 5}, "=", sum));
        s.post(s.arithm(sum, ">", 2));
        s.propagate();
        Assert.assertEquals(sum.isInstantiated(), true);
    }

    @Test(groups="1s", timeOut=60000)
    public void testJG3() throws ContradictionException {
        Solver s = new Solver();
        IntVar var = s.intVar("int", 0, 2, true);
        IntVar view = s.intEqView(var);
        IntVar sum = s.intVar("sum", 0, 6, true);
        s.post(s.scalar(new IntVar[]{view, var}, new int[]{1, 5}, "=", sum));
        s.post(s.arithm(sum, ">", 2));
        s.propagate();
        Assert.assertEquals(sum.isInstantiated(), true);
    }

    @Test(groups="1s", timeOut=60000)
    public void testJG4() throws ContradictionException {
        Solver s = new Solver();
        IntVar var = s.intVar("int", 0, 2, true);
        IntVar view = s.intMinusView(var);
        IntVar sum = s.intVar("sum", 0, 6, true);
        s.post(s.scalar(new IntVar[]{view, var}, new int[]{1, 5}, "=", sum));
        s.post(s.arithm(sum, ">", 2));
        s.propagate();
        Assert.assertEquals(sum.isInstantiated(), true);
    }

    @Test(groups="1s", timeOut=60000)
    public void testvanH() {
        Solver solver = new Solver();
        BoolVar x1 = solver.boolVar("x1");
        BoolVar x2 = solver.boolNotView(x1);
        BoolVar x3 = solver.boolVar("x3");
        IntVar[] av = new IntVar[]{x1, x2, x3};
        int[] coef = new int[]{5, 3, 2};
        solver.post(solver.scalar(av, coef, ">=", 7));
        try {
            solver.propagate();
        } catch (Exception ignored) {
        }
        Assert.assertTrue(x3.isInstantiated());
        Assert.assertEquals(x3.getValue(), 1);
    }
}
