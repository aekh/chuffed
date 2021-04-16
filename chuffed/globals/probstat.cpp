#include <chuffed/core/propagator.h>
#include <stdlib.h>

class VarianceInt : public Propagator {
public:
  int const N;
  IntVar *y;
  vec<IntVar *> x;
  int scale;
  int mode;

  Tint ub_idx = NULL;
  Tint lb_idx = NULL;

  VarianceInt(IntVar *_y, vec<IntVar *> &_x, int _scale, int _mode) :
      N(_x.size()), y(_y), x(_x), scale(_scale), mode(_mode) {
    priority = 1;
    if (mode == 1) {
      for (int i = 0; i < N; i++) x[i]->attach(this, i, EVENT_LU);
      y->attach(this, N, EVENT_F);
    } else if (mode == 2) {
      for (int i = 0; i < N; i++) x[i]->attach(this, i, EVENT_F);
      y->attach(this, N, EVENT_F);
    } else {
      for (int i = 0; i < N; i++) x[i]->attach(this, i, EVENT_F);
      y->attach(this, N, EVENT_F);
    }
  }

  void wakeup(int i, int c) {
    if (mode == 1) {
      pushInQueue();
//      if ((!ub_idx || !lb_idx) ||
//		      (i == ub_idx && c == EVENT_U) ||
//          (i == lb_idx && c == EVENT_L)) {
//      }
		} else if (mode == 2) {
		  pushInQueue();
    } else {
		  pushInQueue();
		}
  }


  bool propagate() {
    if (mode == 2) {
      return chop_prop();
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
    bool all_fixed = true;
    for (int i = 0; i < N; i++) { // O(N)
      if (!x[i]->isFixed()) {
        all_fixed = false;
        break;
      }
    }
    if (all_fixed) {
      return checking_prop();
    }

//    function binary_search(A, n, T) is
//      L := 0
//      R := n − 1
//      while L ≤ R do
//        m := floor((L + R) / 2)
//        if A[m] < T then
//          L := m + 1
//        else if A[m] > T then
//          R := m − 1
//        else:
//          return m
//      return unsuccessful

    int64_t L = 0;
    for (auto i = 0; i < N; ++i) L += x[i]->getMin(); // O(N)
    int64_t R = 0;
    for (auto i = 0; i < N; ++i) R += x[i]->getMax(); // O(N)

    while (L <= R) { // O(log sup x - inf x)
      int64_t m = (L + R)/2; // round down
      int64_t mR = m+1; // round up to next
      if (L+1 == R) { // if L+1 = R < 0
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

      if (var == 0 || varR == 0) {
        return true; // no point in propagating var >= 0
      } else if (var > varR && R != mR) {
        L = mR;
      } else if (var < varR && L != m) {
        R = m;
      } else {
        if (var > varR) {
          var = varR;
          m = mR;
        }

        // calculate variance lb
        long double mult = (long double) 1 / (long double) (N*N*N);
        long double variance_f = mult * (long double) var;
        auto variance = (int64_t) (variance_f * scale);

        // set y
        if(y->setMinNotR(variance)) {
          Clause* r = nullptr;
          if(so.lazy) {
            // Set up reason
            Lit lit[2*N];
            int lits = 0;
            for(int ii = 0; ii < N; ++ii) {
              if (m < N*x[ii]->getMin()) {
                lit[lits++] = x[ii]->getMinLit();
              } else if (N*x[ii]->getMax() > m) {
                lit[lits++] = x[ii]->getMaxLit();
              } else {
                lit[lits++] = x[ii]->getMinLit();
                lit[lits++] = x[ii]->getMaxLit();
              }
            }
            r = Reason_new(lits+1);
            for(int ii = 0; ii < lits; ++ii) (*r)[ii+1] = lit[ii];

//            r = Reason_new(2*N+1); // FIXME this allocates and sets some same explanations twice!3
//            for(int ii = 0; ii < N; ++ii) {
//              if (m < N*x[ii]->getMin()) {
//                (*r)[ii+1] = x[ii]->getMinLit();
//                (*r)[N+ii+1] = x[ii]->getMinLit();
//              } else if (N*x[ii]->getMax() > m) {
//                (*r)[ii+1] = x[ii]->getMaxLit();
//                (*r)[N+ii+1] = x[ii]->getMaxLit();
//              } else {
//                (*r)[ii+1] = x[ii]->getMinLit();
//                (*r)[N+ii+1] = x[ii]->getMaxLit();
//              }
//            }

          }
          if(!y->setMin(variance, r)) return false;
        }
        return true;
      }
    }
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
    bool all_fixed = true;
    for (int i = 0; i < N; i++) {
      if (!x[i]->isFixed()) {
        all_fixed = false;
        break;
      }
    }
    if (all_fixed) {
      return checking_prop();
    }

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
    // only propagate if all fixed
    for (int i = 0; i < N; i++) {
      if (!x[i]->isFixed()) {
        return true;
      }
    }

    // mean
    int64_t sumx = 0;
    for (int i = 0; i < N; i++) sumx += x[i]->getVal();
    long double mean = (long double) sumx / (long double) N;

    // squared diff
    long double sqdiff = 0;
    for (int i = 0; i < N; i++) {
      long double diff = ( (long double) x[i]->getVal() - mean);
      sqdiff += diff * diff;
    }

    // result
    long double result_f = sqdiff / (long double) N;
    uint64_t result = (int64_t) (result_f * scale);

    //printf("%% sqdiff = %Lf and result = %lld", sqdiff, result);

    // set y
    if(y->setValNotR(result)) {
      Clause* r = nullptr;
      if(so.lazy) {
        // Set up reason
        r = Reason_new(N+1);
        for(int ii = 0; ii < N; ++ii) { (*r)[ii+1] = x[ii]->getValLit(); }
      }
      if(!y->setVal(result, r)) return false;
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

void variance_int(IntVar* y, vec<IntVar*>& x, int scale, int mode) {
  if (x.size() >= 1) new VarianceInt(y, x, scale, mode);
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