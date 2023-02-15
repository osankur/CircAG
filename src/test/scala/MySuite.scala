import java.util.HashMap
import com.microsoft.z3._
// For more information on writing tests, see
// https://scalameta.org/munit/docs/getting-started.html
class MySuite extends munit.FunSuite {
  test("SAT Solver") {
    Global.ToggleWarningMessages(true);
    Log.open("test.log");

    System.out.print("Z3 Major Version: ");
    System.out.println(Version.getMajor());
    System.out.print("Z3 Full Version: ");
    System.out.println(Version.getString());
    System.out.print("Z3 Full Version String: ");
    System.out.println(Version.getFullVersion());

    val cfg = HashMap[String, String]()
    cfg.put("model", "true");
    val ctx = Context(cfg);      
    /* do something with the context */

    val opt = ctx.mkOptimize()

    // Set constraints.
    val xExp : IntExpr = ctx.mkIntConst("x")
    val yExp : IntExpr = ctx.mkIntConst("y")

    opt.Add(ctx.mkEq(ctx.mkAdd(xExp, yExp), ctx.mkInt(10)),
            ctx.mkGe(xExp, ctx.mkInt(0)),
            ctx.mkGe(yExp, ctx.mkInt(0)))

    // Set objectives.
    val mx : Optimize.Handle[IntSort] = opt.MkMaximize(xExp)
    val my : Optimize.Handle[IntSort] = opt.MkMaximize(yExp)

    System.out.println(opt.Check())
    System.out.println(mx)
    System.out.println(my)
    /* be kind to dispose manually and not wait for the GC. */
    ctx.close();      
  }
}