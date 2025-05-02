/// Euclid's algorithm for calculating the GCD of two numbers
#[cfg_attr(kani, kani::ensures(|res|
    if x == 0 && y == 0 {
        *res == 0
    } else {
        *res != 0 && x % *res == 0 && y % *res == 0
    }
))]
pub fn gcd(x: u8, y: u8) -> u8 {
    if x == 0 {
        return y;
    }
    if y == 0 {
        return x;
    }
    let mut max = x;
    let mut min = y;
    if min > max {
        let val = max;
        max = min;
        min = val;
    }

    loop {
        let res = max % min;
        if res == 0 {
            return min;
        }

        max = min;
        min = res;
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Frac {
    pub num: u8,
    pub den: u8,
}

impl Frac {
    /// constructor
    pub fn new(num: u8, den: u8) -> Self {
        Frac { num, den }
    }

    /// Method to simplify fraction
    /// For example, `Frac { num: 10, den: 15 }` gets simplified to
    ///     `Frac { num: 2, num: 3 }`
    #[cfg_attr(kani, kani::ensures(|res| res == self))]
    //#[cfg_attr(kani, kani::ensures(|res| self.num == 0 || self.den == 0 || gcd(res.num, res.den) == 1))]
    pub fn simplify(&self) -> Frac {
        if self.num == 0 || self.den == 0 {
            return *self;
        }
        let gcd = gcd(self.num, self.den);
        Frac::new(self.num / gcd, self.den / gcd)
    }
}

impl PartialEq for Frac {
    fn eq(&self, other: &Self) -> bool {
        if self.den == other.den {
            return self.num == other.num;
        }

        if self.num == other.num {
            if self.num == 0 {
                return true;
            }
            return self.den == other.den;
        }

        // if only one of the two fractions has a zero in the denominator, they
        // are not equal
        if self.den == 0 || other.den == 0 {
            return false;
        }

        // if the integer division is not the same, they are not eqaul
        if self.num / self.den != other.num / other.den {
            return false;
        }

        let self_rem = self.num % self.den;
        let other_rem = other.num % other.den;

        match (self_rem == 0, other_rem == 0) {
            (true, true) => return true,
            (true, false) | (false, true) => return false,
            (false, false) => Frac::new(self.den, self_rem) == Frac::new(other.den, other_rem),
        }
    }
}

#[cfg(kani)]
mod kani_checks {
    use super::*;

    #[kani::proof_for_contract(gcd)]
    #[kani::unwind(11)]
    fn check_gcd_contract() {
        gcd(kani::any(), kani::any());
    }

    #[kani::proof_for_contract(Frac::simplify)]
    #[kani::unwind(11)]
    fn check_simplify_no_stubbing() {
        let num: u8 = kani::any();
        let den: u8 = kani::any();
        let frac = Frac::new(num, den);
        frac.simplify();
    }

    #[kani::proof_for_contract(Frac::simplify)]
    #[kani::stub_verified(gcd)]
    #[kani::unwind(9)]
    fn check_simplify_stubbing() {
        let num: u8 = kani::any();
        let den: u8 = kani::any();
        let frac = Frac::new(num, den);
        frac.simplify();
    }

    #[kani::proof]
    fn check_zero_fracs_eq() {
        let f1 = Frac::new(0, kani::any_where(|x| *x != 0));
        let f2 = Frac::new(0, kani::any_where(|x| *x != 0));
        assert_eq!(f1, f2);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn check_eq() {
        assert_eq!(Frac::new(15, 10), Frac::new(3, 2));
        assert_eq!(Frac::new(12, 8), Frac::new(3, 2));
        assert_ne!(Frac::new(11, 10), Frac::new(21, 20));
    }

    #[test]
    fn check_simp() {
        let f = Frac::new(4, 66);
        let s = f.simplify();
        println!("{s:?}");
    }
}
