#include <chuffed/core/propagator.h>
#include <stdlib.h>
#include <cfenv>

class VarianceInt : public Propagator {
public:
  int const N;
  IntVar *y;
  vec<IntVar *> x;
  IntVar *s;
  int scale;
  int mode;

  Tint ub_idx = NULL;
  Tint lb_idx = NULL;

  vec<Tint> pos;
  Tint64_t m_global;
  Tint all_fixed;
  Tint subsumed;

  VarianceInt(IntVar *_y, vec<IntVar *> &_x, IntVar *_s, int _scale, int _mode) :
      N(_x.size()), y(_y), x(_x), s(_s), scale(_scale), mode(_mode) {
    priority = 4;
    all_fixed = 0;
    subsumed = 0;
    if (mode == 1) {
      for (int i = 0; i < N; i++) x[i]->attach(this, i, EVENT_LU);
      y->attach(this, N, EVENT_F);
    } else if (mode == 2) {
      pos.growTo(N);
      for (int i = 0; i < N; ++i) pos[i] = 2;
      for (int i = 0; i < N; i++) {
        x[i]->attach(this, i, EVENT_LU);
      }
      y->attach(this, N, EVENT_F);
      s->attach(this, N+1, EVENT_LU);
    } else {
      for (int i = 0; i < N; i++) x[i]->attach(this, i, EVENT_F);
      y->attach(this, N, EVENT_F);
    }
  }

  void wakeup(int i, int c) override {
    if (subsumed) return;
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
    return;

    if (mode == 1) {
      pushInQueue();
//      if ((!ub_idx || !lb_idx) ||
//		      (i == ub_idx && c == EVENT_U) ||
//          (i == lb_idx && c == EVENT_L)) {
//      }
    } else if (mode == 2) {
      if (i >= N || pos[i] == 2 || all_fixed) {
        pushInQueue();
      } else if (pos[i] == 1 && (c & EVENT_L || c & EVENT_F || c & EVENT_LF)) { // lb above mean of min variance
        pushInQueue();
      } else if (pos[i] == 0) { // overlapping mean of min variance
        if (c & EVENT_U && N*x[i]->getMax() < m_global) {
          pushInQueue();
        } else if (c & EVENT_L && m_global < N*x[i]->getMin()) {
          pushInQueue();
        }
      } else if (pos[i] == -1 && (c & EVENT_U || c & EVENT_F || c & EVENT_UF)) { // ub below mean of min variance
        pushInQueue();
      }
    } else {
      pushInQueue();
    }
  }


  bool propagate() override {
//    for (int i = 0; i < N; ++i) printf("%% x[%d] = %d..%d      ", i, x[i]->getMin(), x[i]->getMax());
//    printf("%% y = %d..%d      ", y->getMin(), y->getMax());
//    printf("%% s = %d..%d\n", s->getMin(), s->getMax());

    if (mode == 2) {
      return chop_prop();// && quick_prop();
    }
    if (mode == 1) {
      return quick_prop();
      //    } else if (mode == 2) {
//      return naive_prop();
    } else {
      return checking_prop();
    }
  }

  bool chop_prop() {
    if (all_fixed) return checking_prop();

    int64_t min_sum = 0;
    int64_t min_sum_b = 0;
    for (auto i = 0; i < N; ++i) min_sum_b += x[i]->getMin(); // O(N)
    min_sum = s->getMin();

    int64_t max_sum = 0;
    int64_t max_sum_b = 0;
    for (auto i = 0; i < N; ++i) max_sum_b += x[i]->getMax(); // O(N)
    max_sum = s->getMax();

    int64_t L = min_sum;
    int64_t R = max_sum;

//    printf("%%%%%%%% -------- %%%%%%%%\n");

    while (L <= R) { // O(log sup x - inf x)
//      printf("%% Now?\n");
      int64_t m = (L + R)/2; m = m - (m<0); // round down
      int64_t mR = m+1; // round up to next
      if (m < L || R < m) m = L;
      if (mR < L || R < mR) mR = R;
      if (L + 1 == R) {
        m = L;
        mR = R;
      }

      int64_t var = 0;
      int64_t varR = 0;

      for (auto i = 0; i < N; ++i) { // O(N)
        int64_t lb = N * x[i]->getMin();
        int64_t ub = N * x[i]->getMax();
        if (m < lb) {
          var += (lb - m) * (lb - m);
        } else if (ub < m) {
          var += (ub - m) * (ub - m);
        } // else overlap (fractional relaxation)
        if (mR < lb) {
          varR += (lb - mR) * (lb - mR);
        } else if (ub < mR) {
          varR += (ub - mR) * (ub - mR);
        } // else overlap (fractional relaxation)
      }

//      printf("%% L = %lld, \t m = %lld, \t mR = %lld, \t R = %lld, \t var = %lld, varR = %lld\n", L, m, mR, R,
//          (int64_t) (((long double) var / (long double) (N*N*N)) * scale),
//          (int64_t) (((long double) varR / (long double) (N*N*N)) * scale));

      if (var == 0 || varR == 0) {
//        printf("%% var = 0!!..\n");
        return true; // no point in propagating var >= 0
      } else if (var > varR && R > mR) {
//        printf("%% L = mR!!..\n");
        L = mR;
      } else if (var < varR && L < m) {
//        printf("%% R = m!!..\n");
        R = m;
      } else { // runs once!
//        printf("%% else!!..\n");
        if (var > varR) {
          var = varR;
          m = mR;
        }
        m_global = m;

        for (int i = 0; i < N; ++i) {
          if (m < N*x[i]->getMin()) {
            pos[i] = 1;
          } else if (N*x[i]->getMax() < m) {
            pos[i] = -1;
          } else {
            pos[i] = 0;
          }
        }

        // calculate variance lb
        const int reset = std::fegetround();
        std::fesetround(FE_DOWNWARD);
        long double variance_f = (long double) var / (long double) (N*N*N);
        auto variance = (int64_t) (variance_f * scale);
        std:fesetround(reset);

        // set y
        if(y->setMinNotR(variance)) {
//          for (int i = 0; i < N; ++i) printf("%% x[%d] = %d..%d      ", i, x[i]->getMin(), x[i]->getMax());
//          printf("%% y = %d..%d      ", y->getMin(), y->getMax());
//          printf("%% s = %d..%d\n", s->getMin(), s->getMax());
//          printf("%% want to set y to %lld..%d from %d..%d \n", variance, y->getMax(), y->getMin(), y->getMax());
          Clause* r = nullptr;
          if(so.lazy) {
            // Set up reason
            Lit lit[2*N+2];
            int lits = 0;
            for(int ii = 0; ii < N; ++ii) {
              if (m < N*x[ii]->getMin()) { // above
                lit[lits++] = x[ii]->getMinLit();
//                lit[lits++] = x[ii]->getMaxLit();
              } else if (N*x[ii]->getMax() < m) { // below
                lit[lits++] = x[ii]->getMaxLit();
//                lit[lits++] = x[ii]->getMinLit();
              } else {
                //lit[lits++] = x[ii]->getMinLit();
                //lit[lits++] = x[ii]->getMaxLit();
              }
            }
            //if (m == s->getMin()) {
              lit[lits++] = s->getMinLit();
            //} else if (m == s->getMax()) {
              lit[lits++] = s->getMaxLit();
            //}
            r = Reason_new(lits+1);
            for(int ii = 0; ii < lits; ++ii) (*r)[ii+1] = lit[ii];
          }
          //printf("%% blab\n");
          if(!y->setMin(variance, r)) return false;
        }

        //return true;

        // propagate x's
//        printf("  %%   # P # R O P ##\n");
        int64_t mins[N];
        int64_t min_var_sum = 0;
        for (int i = 0; i < N; ++i) { // O(N)
          int64_t xlb = x[i]->getMin();
          int64_t xub = x[i]->getMax();
          if (max_sum - xub + xlb < N*xlb) { // above
            int64_t sub = max_sum_b - xub + xlb;
            if (max_sum < sub) sub = max_sum;
            int64_t diff = N*xlb - sub;
            mins[i] = (diff) * (diff);
            min_var_sum += mins[i];
//            printf("%%   # # ## above sq = %lld, min_var_sum-> = %lld, xlb = %lld, N = %d, max_sum = %lld, xub = %lld\n", mins[i], min_var_sum, xlb, N, max_sum, xub);
          } else if (N*xub < min_sum - xlb + xub) { //below
            int64_t sub = min_sum_b - xlb + xub;
            if (min_sum > sub) sub = min_sum;
            int64_t diff = N*xub - sub;
            mins[i] = (diff) * (diff);
            min_var_sum += mins[i];
//            printf("%%   # # ## BElow sq = %lld, min_var_sum-> = %lld, xlb = %lld, N = %d, min_sum = %lld, xub = %lld\n", mins[i], min_var_sum, xlb, N, min_sum, xub);
          } else { //overlap
            mins[i] = 0;
          }
        }
        printf("%% bad = %lld, vs good = %lld\n", min_var_sum, var);
        min_var_sum = var;


        int64_t n3var_upr = (y->getMax() * N * N * N) / scale;
        for (int i = 0; i < N; ++i) { // O(N)
          int64_t tvar = min_var_sum - mins[i];
//          printf("    %% min_var_sum = %lld, tvar = %lld\n", min_var_sum, tvar);
          int64_t xlb = x[i]->getMin();
          int64_t xub = x[i]->getMax();
          if (max_sum - xub + xlb < N*xlb) { // above
            int64_t diff = N*xub - max_sum;
            int64_t maxsq = (diff) * (diff);
            if (maxsq > n3var_upr - tvar) {
              //printf("%% WE CAN PROP for ABOVE!\n");
              const int reset = std::fegetround();
              std::fesetround(FE_UPWARD);
              //if (n3var_upr < tvar) return false;
              long double sqrt = sqrtl((long double) maxsq - n3var_upr + tvar); // TODO check if this is the correct expression!!
              long double div = (sqrt + max_sum) / N;
              auto upr = (int64_t) floorl(div);
              std::fesetround(reset);
              if(x[i]->setMaxNotR(upr)) {
                printf("%% saved max %lld\n", x[i]->getMax()-upr);
//                for (int i = 0; i < N; ++i) printf("%% x[%d] = %d..%d      ", i, x[i]->getMin(), x[i]->getMax());
//                printf("%% y = %d..%d      ", y->getMin(), y->getMax());
//                printf("%% s = %d..%d\n", s->getMin(), s->getMax());
//                printf("%% -->> want to set x[%d] to %d..%lld from %d..%d \n", i, x[i]->getMin(), upr, x[i]->getMin(), x[i]->getMax());
//                printf("%% min_var_sum = %lld,     tvar = %lld,     diff = %lld,     maxsq = %lld,     sqrt = %Lf,   div = %Lf,     n3var_upr = %lld,     n3var_upr - tvar= %lld,     max_sum = %lld\n", min_var_sum, tvar, diff, maxsq, sqrt, div, n3var_upr, n3var_upr-tvar, max_sum);
                Clause* r = nullptr;
                if(so.lazy) {
                  // Set up reason
                  Lit lit[2*N+2];
                  int lits = 0;
                  for(int ii = 0; ii < N; ++ii) {
                    if (ii == i) {
                      lit[lits++] = x[ii]->getMinLit();
                    } else {
                      lit[lits++] = x[ii]->getMinLit();
                      lit[lits++] = x[ii]->getMaxLit();
                    }
                  }
                  lit[lits++] = s->getMinLit();
                  lit[lits++] = s->getMaxLit();
                  lit[lits++] = y->getMaxLit();
                  r = Reason_new(lits+1);
                  for(int ii = 0; ii < lits; ++ii) (*r)[ii+1] = lit[ii];
                }
                if(!x[i]->setMax(upr, r)) return false;
              }
            }
          } else if (N*xub < min_sum - xlb + xub) { //below
            int64_t diff = N*xlb - min_sum;
            int64_t maxsq = (diff) * (diff);
            if (maxsq > n3var_upr - tvar) {
              const int reset = std::fegetround();
              std::fesetround(FE_UPWARD);
              long double sqrt = - sqrtl((long double) n3var_upr - tvar + maxsq); // FIXME there is a bug here!
              std::fesetround(FE_DOWNWARD);
              long double div = (sqrt + min_sum) / (long double) N;
              auto lwr = (int64_t) ceill(div);
              std::fesetround(reset);
              if(x[i]->setMinNotR(lwr)) {
                printf("%% saved min %lld\n", lwr-x[i]->getMin());
//                printf("%% -->> want to set x[%d] to %lld..%d from %d..%d \n", i, lwr, x[i]->getMax(), x[i]->getMin(), x[i]->getMax());
//                printf("%% min_var_sum = %lld,     tvar = %lld,     diff = %lld,     maxsq = %lld,     sqrt = %Lf,   div = %Lf,     n3var_upr = %lld,     n3var_upr - tvar = %lld,     max_sum = %lld\n", min_var_sum, tvar, diff, maxsq, sqrt, div, n3var_upr, n3var_upr-tvar, max_sum);
                Clause* r = nullptr;
                if(so.lazy) {
                  // Set up reason
                  Lit lit[2*N+2];
                  int lits = 0;
                  for(int ii = 0; ii < N; ++ii) {
                    if (ii == i) {
                      lit[lits++] = x[ii]->getMaxLit();
                    } else {
                      lit[lits++] = x[ii]->getMinLit();
                      lit[lits++] = x[ii]->getMaxLit();
                    }
                  }
                  lit[lits++] = s->getMinLit();
                  lit[lits++] = s->getMaxLit();
                  lit[lits++] = y->getMaxLit();
                  r = Reason_new(lits+1);
                  for(int ii = 0; ii < lits; ++ii) (*r)[ii+1] = lit[ii];
                }
                //if(!x[i]->setMin(lwr, r)) return false;
              }
            }
          }
        }


//        if (m == min_sum) {
//
//        } else if (m == max_sum) {
//
//        } else { // min_sum < m < max_sum
//
//        }
//
//        for (int i = 0; i < N; ++i) { // O(N)
//          if (pos[i] == 0) continue;
//          if (pos[i] == -1) {
//            int64_t nx = x[i]->getMin();
//            int64_t nx_diff = x[i]->getMax() - x[i]->getMin();
//            int64_t nm = m - nx_diff;
//          } else if (pos[i] == 1) {
//
//          }
//        }

        return true;
      }
    }
    printf("%% Hmmm.....\n");
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

  bool quick_prop() {
    if (all_fixed) return checking_prop();

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

  bool checking_prop() {
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

    //printf("%% sqdiff = %Lf and result = %lld", sqdiff, result);

    // set y
    if(y->setValNotR(result)) {
//      for (int i = 0; i < N; ++i) printf("%% x[%d] = %d..%d      ", i, x[i]->getMin(), x[i]->getMax());
//      printf("%% y = %d..%d      ", y->getMin(), y->getMax());
//      printf("%% s = %d..%d\n", s->getMin(), s->getMax());
//      printf("%% want to set y to %lli when it is %d..%d\n", result, y->getMin(), y->getMax());
//      if(x[0]->getVal() == 2 && x[1]->getVal() == 1 && x[2]->getVal() == 3 && x[3]->getVal() == 2 && x[4]->getVal() == 2) printf("%% WARNING HERE WE GO!!!");
      Clause* r = nullptr;
      if(so.lazy) {
        // Set up reason
        r = Reason_new(N+1);
        for(int ii = 0; ii < N; ++ii) { (*r)[ii+1] = x[ii]->getValLit(); }
      }
//      printf("%% blib\n");
      if(!y->setVal(result, r)) return false;
    }
    subsumed = 1;
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