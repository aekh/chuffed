#include <chuffed/core/propagator.h>
#include <stdlib.h>
#include <cfenv>

//int ccc = 0;

class VarianceInt : public Propagator {
public:
  int const N;
  IntVar *y;
  vec<IntVar *> x;
  IntVar *s; // s = sum(x)
  int scale;
  int mode;
  int counter_prop;

  Tint ub_idx = NULL;
  Tint lb_idx = NULL;

  vec<Tint> pos; // if the x's are below (-1), overlapping (0) or above (1) the
                 // mean of lb variance. 2 for unknown.
  Tint64_t Mx; // lowest sum of lb n^3 variance
  Tint64_t MxR; // highest sum of lb n^3 variance
  Tint64_t Vx; // lb n^3 variance
  Tint all_fixed; // true if all x are fixed
  Tint subsumed;

  // Statistics
  uint64_t n_wakeups;
  uint64_t n_runs;
  uint64_t n_prop_v_lb;
  uint64_t n_incons_v_lb;
  uint64_t n_prop_v_fix;
  uint64_t n_incons_v_fix;
  uint64_t n_prop_x_above;
  uint64_t n_incons_x_above;
  uint64_t n_prop_x_below;
  uint64_t n_incons_x_below;
  uint64_t n_prop_x_overlap;
  uint64_t n_incons_x_overlap;

  VarianceInt(IntVar *_y, vec<IntVar *> &_x, IntVar *_s, int _scale, int _mode) :
      N(_x.size()), y(_y), x(_x), s(_s), scale(_scale), mode(_mode),
      n_wakeups(0), n_runs(0), n_prop_v_lb(0), n_incons_v_lb(0),
      n_prop_v_fix(0), n_incons_v_fix(0), n_prop_x_above(0),
      n_incons_x_above(0), n_prop_x_below(0), n_incons_x_below(0),
      n_prop_x_overlap(0), n_incons_x_overlap(0) {
    priority = 3;
    all_fixed = 0;
    subsumed = 0;
    switch (mode) {
      case 1: // version 1
      case 2: // version 1 approx c
      case 3: // version 2
      case 4: // version 2 approx c
        init_v1v2();
        break;
      default: // checking x, filter v
        init_checking();
    }
  }

  void wakeup(int i, int c) override {
    if (subsumed) return;
    n_wakeups++;
    //if (i == N+1 && )
    if (all_fixed == 0 && (c & EVENT_F || c & EVENT_LF || c & EVENT_UF)) {
      int all_fixed_ = 1;
      for (int i = 0; i < N; i++) { // O(N)
        if (!x[i]->isFixed()) {
          all_fixed_ = 0;
          break;
        }
      }
      all_fixed = all_fixed_;
    }
    pushInQueue();
  }

  bool propagate() override {
//    printf("%% running propagate\n");
    n_runs++;
    if (all_fixed) return checking_prop();
    switch (mode) {
      case 1: // version 1
        return prop_var_lb()  &&  prop_x_v1();
      case 2: // version 1 approx c
        return prop_var_lb()  &&  prop_x_v1x();
      case 3: // version 2
        return prop_var_lb()  &&  prop_x_v2();
      case 4: // version 2 approx c
        return prop_var_lb()  &&  prop_x_v2x();
      default: // checking x, filter v
        return checking_prop();
    }
  }

  void printStats() override {
    fprintf(stderr, "%% Spread propagator statistics");
    fprintf(stderr, " for mode %d\n", mode);
    fprintf(stderr, ":\n");
    fprintf(stderr, "%%\t#wakeups: %lld\n", n_wakeups);
    fprintf(stderr, "%%\t#runs: %lld\n", n_runs);
    fprintf(stderr, "%%\t#prop var lb: %lld\n", n_prop_v_lb);
    fprintf(stderr, "%%\t#fail var lb: %lld\n", n_incons_v_lb);
    fprintf(stderr, "%%\t#prop var fixed x: %lld\n", n_prop_v_fix);
    fprintf(stderr, "%%\t#fail var fixed x: %lld\n", n_incons_v_fix);
    fprintf(stderr, "%%\t#prop x above: %lld\n", n_prop_x_above);
    fprintf(stderr, "%%\t#fail x above: %lld\n", n_incons_x_above);
    fprintf(stderr, "%%\t#prop x below: %lld\n", n_prop_x_below);
    fprintf(stderr, "%%\t#fail x below: %lld\n", n_incons_x_below);
    fprintf(stderr, "%%\t#prop x overlap: %lld\n", n_prop_x_overlap);
    fprintf(stderr, "%%\t#fail x overlap: %lld\n", n_incons_x_overlap);
  }

  //------------------//
  // Checking Version // mode = 0
  //------------------//

  void init_checking() {
    for (int i = 0; i < N; i++) x[i]->attach(this, i, EVENT_F);
    y->attach(this, N, EVENT_F);
  }

  bool checking_prop() {
//    printf("%% running checking_prop\n");

    //printf("%% Fixed Proping! variance = %d..%d \n", y->getMin(), y->getMax());
    // only propagate if all fixed
    if (!all_fixed) return true;

    // N*mean
    int64_t sumx = 0;
    for (int i = 0; i < N; i++) {
//      printf("%% asdasd");
//      printf("%% x[%d] = %d..%d\n", i, x[i]->getMin(), x[i]->getMax());
//      printf("%% x[%d] = %d\n", i, x[i]->getVal());
      sumx += x[i]->getVal();
    }

    // N*N * squared diff
    int64_t sqdiff = 0;
    for (int i = 0; i < N; i++) {
      int64_t diff = N * x[i]->getVal() - sumx;
      sqdiff += diff * diff;
    }

    // result
    long double result_f = (long double) sqdiff / (long double) (N*N*N);
    int64_t result = (int64_t) (result_f * scale);

//    for (int i = 0; i < N; ++i) printf("   %% x[%d] = %d..%d      ", i, x[i]->getMin(), x[i]->getMax());
//    printf("%% y = %d..%d      ", y->getMin(), y->getMax());
//    printf("%% s = %d..%d\n", s->getMin(), s->getMax());
//    printf("%% sqdiff = %lld and result_f = %Lf and result_f scaled = %Lf and result = %lld", sqdiff, result_f, result_f * scale, result);
//    printf("   %% want to set y to %lli when it is %d..%d\n", result, y->getMin(), y->getMax());

    // set y
    if(y->setValNotR(result)) {
      n_prop_v_fix++;
      Clause* r = nullptr;
      if(so.lazy) {
        // Set up reason
        r = Reason_new(N+1);
        for(int ii = 0; ii < N; ++ii) { (*r)[ii+1] = x[ii]->getValLit(); }
      }
      if(!y->setVal(result, r)) {
        n_incons_v_fix++;
        return false;
      }
    }
    subsumed = 1;
    return true;
  }

  //-----------//
  // Version 1 // mode = 1
  //-----------//

  void init_v1v2() {
    pos.growTo(N);
    for (int i = 0; i < N; ++i) pos[i] = 2;
    for (int i = 0; i < N; i++) {
      x[i]->attach(this, i, EVENT_LU);
    }
    y->attach(this, N, EVENT_F);
    s->attach(this, N+1, EVENT_LU);
  }

  bool prop_var_lb() {
//    printf("%% running prop_var_lb\n");
    int64_t L = s->getMin(), R = s->getMax();

    // Binary Chop
    while (L <= R) { // O(log sup x - inf x)

//      printf("%% ~~~~> ~~~~> M = %d..%d,   L = %lli,    R = %lli\n", s->getMin(), s->getMax(), L, R);

      int64_t m = (L + R) / 2;
      m = m - (m < 0); // round down
      int64_t mR = m + 1; // round up to next
      if (m < L || R < m) m = L;
      if (mR < L || R < mR) mR = R;
      if (L + 1 == R) {
        m = L; mR = R;
      } // FIXME? d = (R - L) / 2;  m = L+d, mR = m+1

      // calculate variance
      int64_t var = 0, varR = 0;
      for (auto i = 0; i < N; ++i) { // O(N)
        int64_t lb = N * x[i]->getMin(), ub = N * x[i]->getMax();
        if (m < lb)      var += (lb - m) * (lb - m);
        else if (ub < m) var += (ub - m) * (ub - m);
        if (mR < lb)      varR += (lb - mR) * (lb - mR);
        else if (ub < mR) varR += (ub - mR) * (ub - mR);
      }

      // terminate
      if (var == 0 || varR == 0) {
//        return true;
        if (var > varR) {
          var = varR; m = mR;
        }
        Vx = var;

        auto mL = m-1;
        for (; mL > s->getMin(); --mL){
          int var_temp = 0;
          for (auto i = 0; i < N; ++i) { // O(N)
            int64_t lb = N * x[i]->getMin(), ub = N * x[i]->getMax();
            if (mL < lb)      var_temp += (lb - mL) * (lb - mL);
            else if (ub < mL) var_temp += (ub - mL) * (ub - mL);
          }
          if (var != var_temp) {
            break;
          }
        }
        ++mL;
        Mx = mL;

        auto mR = m+1;
        for (; mR < s->getMax(); ++mR){
          int var_temp = 0;
          for (auto i = 0; i < N; ++i) { // O(N)
            int64_t lb = N * x[i]->getMin(), ub = N * x[i]->getMax();
            if (mR < lb)      var_temp += (lb - mR) * (lb - mR);
            else if (ub < mR) var_temp += (ub - mR) * (ub - mR);
          }
          if (var != var_temp) {
            break;
          }
        }
        --mR;
        MxR = mR;

        break;
      }

      // iterate
      if (var > varR && R > mR) L = mR;
      else if (var < varR && L < m) R = m;

      // exit loop for propagation
      else {
        if (var > varR) {
          var = varR; m = mR;
        }
        Vx = var;

        auto mL = m-1;
        for (; mL > s->getMin(); --mL){
          int var_temp = 0;
          for (auto i = 0; i < N; ++i) { // O(N)
            int64_t lb = N * x[i]->getMin(), ub = N * x[i]->getMax();
            if (mL < lb)      var_temp += (lb - mL) * (lb - mL);
            else if (ub < mL) var_temp += (ub - mL) * (ub - mL);
          }
          if (var != var_temp) {
            break;
          }
        }
        ++mL;
        Mx = mL;

        auto mR = m+1;
        for (; mR < s->getMax(); ++mR){
          int var_temp = 0;
          for (auto i = 0; i < N; ++i) { // O(N)
            int64_t lb = N * x[i]->getMin(), ub = N * x[i]->getMax();
            if (mR < lb)      var_temp += (lb - mR) * (lb - mR);
            else if (ub < mR) var_temp += (ub - mR) * (ub - mR);
          }
          if (var != var_temp) {
            break;
          }
        }
        --mR;
        MxR = mR;

        break;
      }
    }

    // update positions
    for (int i = 0; i < N; ++i) { // O(N)
      if (MxR < N*x[i]->getMin())     pos[i] =  1; // TODO: changed to MxR from Mx, correct?
      else if (N*x[i]->getMax() < Mx) pos[i] = -1;
      else                            pos[i] =  0;
    }

    // calculate variance lb
    const int reset = std::fegetround();
    std::fesetround(FE_DOWNWARD);
    long double variance_f = (long double) Vx / (long double) (N*N*N);
    auto variance = (int64_t) (variance_f * scale);
    std:fesetround(reset);

    // set y
    if(y->setMinNotR(variance)) {
      n_prop_v_lb++;
      Clause* r = nullptr;
      if(so.lazy) {
        // Set up reason
        Lit lit[2*N+2];
        int lits = 0;
        for(int ii = 0; ii < N; ++ii) {
          if (pos[ii] == 1)       lit[lits++] = x[ii]->getMinLit(); // TODO: changed to MxR from Mx, correct?
          else if (pos[ii] == -1) lit[lits++] = x[ii]->getMaxLit();
        }
        if (Mx == s->getMin()) lit[lits++] = s->getMinLit();
        if (MxR == s->getMax()) lit[lits++] = s->getMaxLit(); // TODO: changed to MxR from Mx, correct?
        r = Reason_new(lits+1);
        for(int ii = 0; ii < lits; ++ii) (*r)[ii+1] = lit[ii];
      }
      if(!y->setMin(variance, r)) {
        n_incons_v_lb++;
        return false;
      }
    }
    return true;
  }

  bool prop_x_v1() {
//    printf("%% running prop_x_v1\n");
//    if (all_fixed) return checking_prop();

    for (int i = 0; i < N; i++) {
      assert(pos[i] != 2);

      // overlap
      if (pos[i] == 0) {
        if (!prop_x_v1_O(i)) return false;
      }

      // above or below
      else {
        if (!prop_x_v1_AB(i)) return false;
      }
    }
    return true;
  }

  bool prop_x_v1_O(int i) {
//    printf("%% running prop_x_v1_O\n");

    const int reset = std::fegetround();

    std::fesetround(FE_DOWNWARD);
    auto Lx = fmax((long double) (N*x[i]->getMin()),
                   (long double) s->getMin());
    std::fesetround(FE_UPWARD);
    auto VxU = floorl(
        (long double) ((int64_t) (y->getMax() + 1) * N * N * N) /
        (long double) scale);
    auto sqrtK = sqrtl(VxU - (long double) Vx);
    auto x_lb = (int) ceil( (Lx - sqrtK ) / N);

    auto Ux = fmax((long double) (N*x[i]->getMax()),
                   (long double) s->getMax());
    std::fesetround(FE_DOWNWARD);
    auto x_ub = (int) floor( (Ux + sqrtK) / N);

    printf("%%\t Ux = %LF, VxU = %LF, sqrtK = %LF, x_ub = %d, yGetMax = %LF, scale = %LF, y->getMax() = %d, Vx = %lld, N = %d, y->getMin() = %d\n",
        Ux, VxU, sqrtK, x_ub, (long double) ((int64_t) (y->getMax() + 1) * N * N * N), (long double) scale, y->getMax(), Vx.v, N, y->getMin());

    // explanation
    Clause *r = nullptr;
    if (x[i]->setMinNotR(x_lb) || x[i]->setMaxNotR(x_ub)) {
      n_prop_x_overlap++;
      if (so.lazy) {
        // Set up reason
        Lit lit[2 * N + 6];
        int lits = 0;

        // not needed
        for(int ii = 0; ii < N; ++ii) {
          //if (pos[ii] == 1)
            lit[lits++] = x[ii]->getMinLit();
          //else if (pos[ii] == -1)
            lit[lits++] = x[ii]->getMaxLit();
        }

        // For using Lx and Ux
        //if ((int64_t)Ux == N*x[i]->getMax())
        lit[lits++] = x[i]->getMaxLit();
        //else
        lit[lits++] = s->getMaxLit();
        //if ((int64_t)Lx == N*x[i]->getMin())
        lit[lits++] = x[i]->getMinLit();
        //else
        lit[lits++] = s->getMinLit();

        // For using Vx and VxU
        lit[lits++] = y->getMaxLit();
        lit[lits++] = y->getMinLit();
        r = Reason_new(lits + 1);
        for (int ii = 0; ii < lits; ++ii) (*r)[ii + 1] = lit[ii];
      }
    }

    // prune
    if (x[i]->setMinNotR(x_lb)) {
      std::fesetround(reset);
      if (!x[i]->setMin(x_lb, r)) {
        printf("%%\t lb false\n");
        printf("%%\t lb is %d want to set to %d\n", x[i]->getMin(), x_lb);
        n_incons_x_overlap++;
        return false;
      }
    }
    if (x[i]->setMaxNotR(x_ub)) {
      std::fesetround(reset);
      if (!x[i]->setMax(x_ub, r)) {
        printf("%%\t ub false\n");
        printf("%%\t ub is %d want to set to %d\n", x[i]->getMax(), x_ub);
        n_incons_x_overlap++;
        return false;
      }
    }
    return true;
  }

  bool prop_x_v1_AB(int i) {
    assert(false && "TODO, not implemented yet");
  }

  //------------------//
  // Version 1 Approx // mode = 2
  //------------------//

  bool prop_x_v1x(){
//    printf("%% running prop_x_v1x\n");
//    if (all_fixed) return checking_prop();

    int n_AuB = N;
    for (int j = 0; j < N; j++) {
      assert(pos[j] != 2);
      if (pos[j] == 0) n_AuB--;
    }

    int64_t b_lb = 0;
    for (int j = 0; j < N; ++j) {
      if (j != 0) b_lb += n_AuB * x[j]->getMin();
      if (pos[j] == 0) b_lb += 2 * N * x[j]->getMin();
    }

    int64_t b_ub = 0;
    for (int j = 0; j < N; ++j) {
      if (j != 0) b_lb += n_AuB * x[j]->getMax();
      if (pos[j] == 0) b_lb += 2 * N * x[j]->getMax();
    }

    int64_t c_lb = 0;
    int max_lb_x = 0;
    for (int j = 0; j < N; ++j) {
      if (x[j]->getMin() > max_lb_x) max_lb_x = x[j]->getMin();
      c_lb += x[j]->getMin();
    }
    c_lb -= max_lb_x;
    c_lb = c_lb * c_lb;

    // explanation
    Clause *r = nullptr;
    if (so.lazy) {
      // Set up reason
      Lit lit[2 * N + 1];
      int lits = 0;

      // For using all x's ub's and lb's
      for(int ii = 0; ii < N; ++ii) {
        lit[lits++] = x[ii]->getMinLit();
        lit[lits++] = x[ii]->getMaxLit();
      }

      // For using VxU
      lit[lits++] = y->getMaxLit();

      r = Reason_new(lits + 1);
      for (int ii = 0; ii < lits; ++ii) (*r)[ii + 1] = lit[ii];
    }

    for (int i = 0; i < N; i++) {
      // overlap
      if (pos[i] == 0) {
        if (!prop_x_v1_O(i)) return false;
      }

      // above or below
      else {
        if (i > 0) {
          b_lb -= n_AuB * x[i]->getMin();
          b_lb += n_AuB * x[i-1]->getMin();
          b_ub -= n_AuB * x[i]->getMax();
          b_ub += n_AuB * x[i-1]->getMax();
        }
        if (!prop_x_v1x_AB(i, n_AuB, b_lb, b_ub, c_lb, r)) return false;
      }
    }
    return true;
  }

  bool prop_x_v1x_AB(int i, int n_AuB, int64_t b_lb, int64_t b_ub,
      int64_t c_lb, Clause *r) {
//    printf("%% running prop_x_v1x_AB\n");

    const int reset = std::fegetround();

    int64_t a = N^2 - 2*N + n_AuB;

    std::fesetround(FE_UPWARD);
    auto VxU = floorl(
        (long double) ((int64_t) (y->getMax() + 1) * N * N * N) /
        (long double) scale);
    auto sqrtExprL = sqrtl(4*a*VxU + 4*a*c_lb + b_ub*b_ub);
    auto sqrtExprU = sqrtl(4*a*VxU + 4*a*c_lb + b_ub*b_ub);

    std::fesetround(FE_DOWNWARD);
    auto x_lb = (int) ceill( (-sqrtExprL - b_ub) / 2*a);

    std::fesetround(FE_UPWARD);
    auto x_ub = (int) floorl( (sqrtExprU - b_lb) / 2*a);

    // Prune
    if (x[i]->setMinNotR(x_lb) || x[i]->setMaxNotR(x_ub)) {
      if (pos[i] == 1) n_prop_x_above++;
      else if (pos[i] == -1) n_prop_x_below++;
    }

    if (x[i]->setMinNotR(x_lb)) {
      std::fesetround(reset);
      if (!x[i]->setMin(x_lb, r)) {
        if (pos[i] == 1) n_incons_x_above++;
        else if (pos[i] == -1) n_incons_x_below++;
        return false;
      }
    }
//    if (x[i]->setMaxNotR(x_ub)) {
//      std::fesetround(reset);
//      if (!x[i]->setMax(x_ub, r)) {
//        if (pos[i] == 1) n_incons_x_above++;
//        else if (pos[i] == -1) n_incons_x_below++;
//        return false;
//      }
//    }
    return true;
  }

  //-----------//
  // Version 2 // mode = 3
  //-----------//

  bool prop_x_v2(){
    assert(false && "TODO, not implemented yet");
  }

  //------------------//
  // Version 2 Approx // mode = 4
  //------------------//

  bool prop_x_v2x(){
    assert(false && "TODO, not implemented yet");
  }

  bool prop_x() {

    // TODO only perfect precision when N*N*N < scale, perhaps okay for rough precision.
    const int reset = std::fegetround();
    std::fesetround(FE_UPWARD);
    auto n3var_upr = (int64_t) floorl(
        (long double) ((y->getMax() + 1) * N * N * N) /
        (long double) scale);

    int64_t min_sum = s->getMin(), max_sum = s->getMax();
    int64_t min_sum_b = 0, max_sum_b = 0;
    for (int i = 0; i < N; ++i) {
      min_sum_b += x[i]->getMin();
      max_sum_b += x[i]->getMax();
    }


    if (mode == 2) {
      // propagate x's
      int64_t mins[N];
      int64_t min_var_sum = 0;
      for (int i = 0; i < N; ++i) { // O(N)
        int64_t xlb = x[i]->getMin();
        int64_t xub = x[i]->getMax();
        int64_t Sub = max_sum_b - xub + xlb;
        int64_t Slb = min_sum_b - xlb + xub;
        if (Sub < N * xlb) { // above
          int64_t diff = N * xlb - Sub;
          mins[i] = (diff) * (diff);
          min_var_sum += mins[i];
        } else if (N * xub < Slb) { //below
          int64_t diff = N * xub - Slb;
          mins[i] = (diff) * (diff);
          min_var_sum += mins[i];
        } else { //overlap
          mins[i] = 0;
        }
      }

      for (int i = 0; i < N; ++i) { // O(N)
        int64_t remvar = min_var_sum - mins[i];
        int64_t xlb = x[i]->getMin();
        int64_t xub = x[i]->getMax();
        int64_t Sub = max_sum_b - xub + xlb;
        short above = Sub < N * xlb;
        int64_t Slb = min_sum_b - xlb + xub;
        short below = N * xub < Slb;
        std::fesetround(FE_UPWARD);
        long double sqrt = sqrtl(n3var_upr - remvar);
        if (above) {
          int64_t cand = max_sum;
          if (abs(N * xub - max_sum) > abs(N * xub - Slb)) cand = min_sum;
          std::fesetround(FE_UPWARD);
          long double div = (cand + sqrt) / N;
          auto upr = (int64_t) floorl(div);
          if (n3var_upr < remvar) upr = x[i]->getMin() - 1;
          if (x[i]->setMaxNotR(upr)) {
            Clause *r = nullptr;
            if (so.lazy) {
              // Set up reason
              Lit lit[2 * N + 2 + 2];
              int lits = 0;
              for (int ii = 0; ii < N; ++ii) {
                if (ii == i) continue;
                lit[lits++] = x[ii]->getMinLit();
                lit[lits++] = x[ii]->getMaxLit();
              }
              lit[lits++] = s->getMinLit();
              lit[lits++] = s->getMaxLit();
              lit[lits++] = y->getMaxLit();
              r = Reason_new(lits + 1);
              for (int ii = 0; ii < lits; ++ii) (*r)[ii + 1] = lit[ii];
            }
            std::fesetround(reset);
            if (!x[i]->setMax(upr, r)) return false;
          }
        }
        if (below) {
          int64_t cand = min_sum;
          //if (abs(N*xlb - min_sum) > abs(N*xlb - max_sum)) cand = max_sum;
          std::fesetround(FE_DOWNWARD);
          long double div = (cand - sqrt) / N;
          auto lwr = (int64_t) ceill(div);
          if (n3var_upr < remvar) lwr = x[i]->getMax() + 1;
          if (x[i]->setMinNotR(lwr)) {
            Clause *r = nullptr;
            if (so.lazy) {
              // Set up reason
              Lit lit[2 * N + 2];
              int lits = 0;
              for (int ii = 0; ii < N; ++ii) {
                if (ii == i) continue;
                lit[lits++] = x[ii]->getMinLit();
                lit[lits++] = x[ii]->getMaxLit();
              }
              lit[lits++] = s->getMinLit();
              lit[lits++] = s->getMaxLit();
              lit[lits++] = y->getMaxLit();
              r = Reason_new(lits + 1);
              for (int ii = 0; ii < lits; ++ii) (*r)[ii + 1] = lit[ii];
            }
            std::fesetround(reset);
            if (!x[i]->setMin(lwr, r)) return false;
          }
        }
      }
    } else { // mode is 3
      int64_t n3s = n3var_upr - Vx;
      for(int i = 0; i < N; ++i) {
        int64_t xub = x[i]->getMax();
        int64_t xlb = x[i]->getMin();

        int64_t Sub = max_sum_b - xub + xlb;
        int64_t Slb = min_sum_b - xlb + xub;

//        if (Mx.v != MxR.v){
//          printf("%% Mx = %lli, MxR = %lli\n", Mx.v, MxR.v);
//        }

        //overlap M
        if (pos[i] == 0) { // TODO: Why Mx.v here but not elsewhere?
          std::fesetround(FE_UPWARD);
          long double sqrt = sqrtl(n3s);

          int64_t Mxlb = s->getMin();
          if (Mxlb < N*xlb) Mxlb = N*xlb;
          std::fesetround(FE_DOWNWARD);
          auto n_xlb = (int64_t) ceill((Mxlb - sqrt) / N );

          int64_t Mxub = s->getMax();
          if (N*xub < Mxub) Mxub = N*xub;
          std::fesetround(FE_UPWARD);
          auto n_xub = (int64_t) floorl((Mxub + sqrt) / N );

          // explanation
          Clause *r = nullptr;
          if (x[i]->setMinNotR(n_xlb) || x[i]->setMaxNotR(n_xub)) {
            if (so.lazy) {
              // Set up reason
              Lit lit[2 * N + 4];
              int lits = 0;
              for (int ii = 0; ii < N; ++ii) {
//                if (ii == i) continue; // TODO: correct to ignore x[i] in expl?
                lit[lits++] = x[ii]->getMinLit();
                lit[lits++] = x[ii]->getMaxLit();
              }
              lit[lits++] = s->getMinLit();
              lit[lits++] = s->getMaxLit();
              lit[lits++] = y->getMaxLit();
              lit[lits++] = y->getMinLit();
              r = Reason_new(lits + 1);
              for (int ii = 0; ii < lits; ++ii) (*r)[ii + 1] = lit[ii];
            }
          }

          // prune
          if (x[i]->setMinNotR(n_xlb)) {
            std::fesetround(reset);
            if (!x[i]->setMin(n_xlb, r)) return false;
          }
          if (x[i]->setMaxNotR(n_xub)) {
            std::fesetround(reset);
            if (!x[i]->setMax(n_xub, r)) return false;
          }
        }

        //above M
        else if (pos[i] == 1 && (Mx.v == MxR.v)) {
          int64_t sq = (N*xub - Mx);
          sq = sq * sq;
          std::fesetround(FE_UPWARD);
          long double sqrt = sqrtl(n3s + sq);
          auto n_xub = (int64_t) floorl((Mx + sqrt) / N );

          // explanation
          Clause *r = nullptr;
          if (x[i]->setMaxNotR(n_xub)) {
            if (so.lazy) {
              //printf("constraint if ");
              // Set up reason
              Lit lit[2 * N + 4];
              int lits = 0;
              for (int ii = 0; ii < N; ++ii) {
                lit[lits++] = x[ii]->getMinLit();
//                if (ii != i) lit[lits++] = x[ii]->getMaxLit();
                lit[lits++] = x[ii]->getMaxLit();
//                printf("x[%d] <= %d /\\ ", ii, x[ii]->getMax());
//                printf("x[%d] >= %d /\\ ", ii, x[ii]->getMin());
              }
              lit[lits++] = s->getMinLit();
              lit[lits++] = s->getMaxLit();
              lit[lits++] = y->getMaxLit();
              lit[lits++] = y->getMinLit();
//              printf("s <= %d /\\ ", s->getMax());
//              printf("s >= %d /\\ ", s->getMin());
//              printf("variance <= %d /\\ ", y->getMax());
//              printf("variance >= %d", y->getMin());
//              printf(" then x[%d] <= %lli endif; /* SATCHEC */ \n", i, n_xub);

              r = Reason_new(lits + 1);
              for (int ii = 0; ii < lits; ++ii) (*r)[ii + 1] = lit[ii];
            }
          }

          // prune
          if (x[i]->setMaxNotR(n_xub)) {
            std::fesetround(reset);
            printf("COUNTZ %lli\n", ++counter_prop);
//            printf("===\n");
//            for (int i = 0; i < N; ++i) printf("   %% x[%d] = %d..%d      ", i, x[i]->getMin(), x[i]->getMax());
//            printf("%% y = %d..%d      ", y->getMin(), y->getMax());
//            printf("%% s = %d..%d\n", s->getMin(), s->getMax());
//            printf("%% Mx = %lld and sq = %lli and sqrt = %Lf and n_xub = %lld and Vx = %lli and n3var_upr = %lli and n3s = %lli", Mx.v, sq, sqrt, n_xub, Vx.v, n3var_upr, n3s);
//            printf("   %% want to set x[%d] to %d..>%lli< when it is %d..%d\n", i, x[i]->getMin(), n_xub, x[i]->getMin(), x[i]->getMax());
            if (!x[i]->setMax(n_xub, r)) return false;
          }
        }
        //below M
        else if (pos[i] == -1 && (Mx.v == MxR.v)) {
          int64_t sq = (N*xlb - Mx);
          sq = sq * sq;
          std::fesetround(FE_DOWNWARD);
          long double sqrt = sqrtl(n3s + sq);
          auto n_xlb = (int64_t) ceill((Mx - sqrt) / N );

          // explanation
          Clause *r = nullptr;
          if (x[i]->setMinNotR(n_xlb)) {
            if (so.lazy) {
              // Set up reason
              Lit lit[2 * N + 4];
              int lits = 0;
              for (int ii = 0; ii < N; ++ii) {
//                if (ii != i) lit[lits++] = x[ii]->getMinLit();
                lit[lits++] = x[ii]->getMinLit();
                lit[lits++] = x[ii]->getMaxLit();
              }
              lit[lits++] = s->getMinLit();
              lit[lits++] = s->getMaxLit();
              lit[lits++] = y->getMaxLit();
              lit[lits++] = y->getMinLit();
              r = Reason_new(lits + 1);
              for (int ii = 0; ii < lits; ++ii) (*r)[ii + 1] = lit[ii];
            }
          }

          // prune
          if (x[i]->setMinNotR(n_xlb)) {
            printf("COUNTZ %lli\n", ++counter_prop);
            std::fesetround(reset);
            if (!x[i]->setMin(n_xlb, r)) return false;
          }
        }
//        if pos[i] != -1,0,1 then do nothing
      }
    }
    std::fesetround(reset);
    return true;
  }

//  bool naive_prop() {
//    // mean
//    int64_t sumx_ub = 0;
//    for (int i = 0; i < N; i++) sumx_ub += x[i]->getMax();
//    long double mean_ub = (long double) sumx_ub / (long double) N;
//
//    int64_t sumx_lb = 0;
//    for (int i = 0; i < N; i++) sumx_lb += x[i]->getMin();
//    long double mean_lb = (long double) sumx_lb / (long double) N;
//
//    // squared diff
//    long double sqdiff_ub = 0;
//    for (int i = 0; i < N; i++) {
//      long double diff = (long double) x[i]->getMin() - mean_ub;
//      sqdiff += diff * diff;
//    }
//
//    // result
//    long double result_f = sqdiff / (long double) N;
//    uint64_t result = (int64_t) (result_f * scale);
//
//    //printf("%% sqdiff = %Lf and result = %lld", sqdiff, result);
//
//    // set y
//    if(y->setValNotR(result)) {
//      Clause* r = nullptr;
//      if(so.lazy) {
//        // Set up reason
//        r = Reason_new(N+1);
//        for(int ii = 0; ii < N; ++ii) { (*r)[ii+1] = x[ii]->getValLit(); }
//      }
//      if(!y->setVal(result, r)) return false;
//    }
//    return true;
//  }

  bool prop_var_ub() {
    // Popoviciu's inequality on variances
    int64_t min_lb = INT64_MAX;
    int64_t max_ub = INT64_MIN;
    for (int i = 0; i < N; i++) {
      int64_t lb = x[i]->getMin();
      int64_t ub = x[i]->getMax();
      if (lb < min_lb) {
        min_lb = lb;
        lb_idx = i;
      }
      if (ub > max_ub) {
        max_ub = ub;
        ub_idx = i;
      }
    }
    int64_t sqdiff = (max_ub - min_lb) * (max_ub - min_lb);
    long double var_ub_f = (long double) sqdiff / (long double) 4;
    int64_t var_ub = (int64_t) (var_ub_f * scale);

    // set y
    if(y->setMaxNotR(var_ub)) {
      Clause* r = nullptr;
      if(so.lazy) {
        // Set up reason
        r = Reason_new(2*N+1);
        for(int ii = 0; ii < N; ++ii) {
          (*r)[ii+1] = x[ii]->getMaxLit();
          (*r)[N+ii+1] = x[ii]->getMinLit();
        }
      }
      if(!y->setMax(var_ub, r)) return false;
    }
    return true;
  }
};


class CovSq : public Propagator {
public:
	int const N;
	IntVar* y;
	vec<IntVar*> x;
	int scale;

	CovSq(IntVar* _y, vec<IntVar*>& _x, int _scale)	:
	  N(_x.size()), y(_y), x(_x), scale(_scale) {
    priority = 1;
		for (int i = 0; i < N; i++) x[i]->attach(this, i, EVENT_F);
		y->attach(this, N, EVENT_F);
	}

//	void wakeup(int i, int c) {
//		pushInQueue();
//	}

	bool propagate() {
    for (int i = 0; i < N; i++) {
      if (!x[i]->isFixed()) {
        return true;
      }
    }
    printf("%% actual prop starting..\n");
    long double result_f;
		int64_t result = 0;
		int64_t dividend = 0;
	  int64_t divisor = 0;
    int64_t sumx = 0;
    for (int i = 0; i < N; i++) sumx += x[i]->getVal();
    divisor = N * sumx * sumx;
    for (int i = 0; i < N; i++) {
    	int64_t diff = N * x[i]->getVal() - sumx;
    	dividend += diff * diff;
    }
    result_f = (dividend * scale) / divisor;
    result = (int64_t) result_f;
    printf("%% %lli / %lli = %Lf, then = %lld", dividend, divisor, result_f, result);
    printf("%% %lld \n", result);
    if(y->setValNotR(result)) {
      printf("%% setValNotR\n");
      Clause* r = nullptr;
      if(so.lazy) {
        // Set up reason
        r = Reason_new(N+1);
        for(int ii = 0; ii < N; ++ii) { (*r)[ii+1] = x[ii]->getValLit(); }
      }
      if(!y->setVal(result, r)) return false;
    }
    return true;
    //return y->setVal(result);
	}

//	void clearPropState() {
//		in_queue = false;
//	}
//
//	int checkSatisfied() {
//		return 1;
//	}

};

void covsq(IntVar* y, vec<IntVar*>& x, int scale) {
  new CovSq(y, x, scale);
}

void variance_int(IntVar* y, vec<IntVar*>& x, IntVar* s, int scale, int mode) {
  if (x.size() >= 1) new VarianceInt(y, x, s, scale, mode);
}


class SpreadFast : public Propagator {
public:
  int const N;
  int const vals;
  vec<IntVar *> x;
  vec<IntVar *> cl;
  IntVar *mean;
  IntVar *stdev;
  IntVar *median;
  int scale;

  Tint lb;
  Tint ub;

  SpreadFast(vec<IntVar *> &_x, vec<IntVar *> &_cl,
      IntVar *_mean, IntVar *_stdev, IntVar *_median,
      int _scale) :
  N(_x.size()), vals(_cl.size()), x(_x), cl(_cl),
  mean(_mean), stdev(_stdev), median(_median),
  scale(_scale) {
    priority = 1;
    int64_t _ub = INT64_MIN;
    int64_t _lb = INT64_MAX;
    for (int i = 0; i < N; ++i) {
      x[i]->attach(this, i, EVENT_F);
      if (x[i]->getMax() > _ub) _ub = x[i]->getMax();
      if (x[i]->getMin() < _lb) _lb = x[i]->getMin();
    }
    for (int i = 0; i < vals; ++i) cl[i]->attach(this, i, EVENT_F);
    mean->attach(this, N, EVENT_F);
    stdev->attach(this, N+1, EVENT_F);
    median->attach(this, N+2, EVENT_F);
    ub = _ub;
    lb = _lb;
  }

  bool propagate() {
    auto mean_ub_f = (long double) mean->getMax() / (long double) scale;
    auto mean_lb_f = (long double) mean->getMin() / (long double) scale;
    auto mua = (int64_t) ceil(mean_ub_f - lb);
    auto bmu = ub - (int64_t) mean_lb_f;





    return true;
  }

};

void spread_fast(vec<IntVar *> &x, vec<IntVar *> &cl,
    IntVar *mean, IntVar *stdev, IntVar *median,
    int scale) {
  new SpreadFast(x, cl, mean, stdev, median, scale);
}


class SpreadBounds : public Propagator {
public:
  int const N;
  vec<IntVar *> x;
  IntVar *mean;
  IntVar *stdev;
  IntVar *median;
  int scale;

  vec<Tint> _bounds;

  static int compare (const void * a, const void * b)
  {
    return ( *(int*)a - *(int*)b );
  }

  static void get_bounds (vec<Tint> *_bounds, vec< vec<int> > *bounds) {
    int len = _bounds->size();
    int arr[len][2];
    int act_len = 0;
    for (auto i = 0; i < len - 1; ++i) {
      if ((*_bounds)[i] != (*_bounds)[i+1]) {
        arr[i][0] = (*_bounds)[i];
        arr[i][1] = (*_bounds)[i+1];
        ++act_len;
      }
    }
    bounds->growTo(act_len);
    printf("%% DAD, act_len = %d\n", act_len);
    for (auto i = 0; i < act_len; ++i) {
      (*bounds)[0].growTo(3);
      *bounds[i][0] = arr[i][0];
      *bounds[i][1] = arr[i][1];
      printf("%% ss\n");
      printf("%% %d = %d..%d\n", i, *bounds[i][0], *bounds[i][1]);
    }
  }

  SpreadBounds(vec<IntVar *> &_x,
      IntVar *_mean, IntVar *_stdev, IntVar *_median, int _scale) :
  N(_x.size()), x(_x),
  mean(_mean), stdev(_stdev), median(_median),
  scale(_scale) {
    priority = 1;
    _bounds.growTo(N*2);
    for (int i = 0; i < N; ++i) {
      x[i]->attach(this, i, EVENT_F);
      _bounds[i] = x[i]->getMin();
      _bounds[N+i] = x[i]->getMax();
    }
    mean->attach(this, N, EVENT_F);
    stdev->attach(this, N+1, EVENT_F);
    median->attach(this, N+2, EVENT_F);

    // sort bounds vector (but still dupes)
    qsort(&_bounds[0], _bounds.size(), sizeof(Tint), compare);

  }

  bool propagate() {
    qsort(&_bounds[0], _bounds.size(), sizeof(Tint), compare);
    vec< vec<int> > bounds;
    get_bounds(&_bounds, &bounds);

    int I = 0; // FIXME

    // optimal value
    // LI1
    // RI1
    // MI1
    // ESI1
    // q-opt and opt
    for (int k = 1; k < I; ++k) {
      //LIk
      //RIk
      //MIk
      //ESIk
      //VIk
      //GCIk
      // q-opt and opt
    }

    // bounds reduction

    return true;
  }
};

void spread_bounds(vec<IntVar *> &x,IntVar *mean, IntVar *stdev, IntVar *median,
                 int scale) {
  new SpreadBounds(x, mean, stdev, median, scale);
}