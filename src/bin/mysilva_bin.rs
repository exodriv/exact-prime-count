use chrono::{DateTime,Local};
use mysilva::*;
const SIGNBIT: i32 = 1 << 31;
type Intervals<'a> = (usize, &'a [usize], usize);
type RegVars<'a> = (u64, usize, &'a mut i64, &'a [i32]);
type P2Vars<'a> = (&'a mut i32, usize);
type S2bVars<'a> = (&'a mut usize, &'a [usize], &'a [i32]);
fn main() {
        let big_primes = prime_table("9");
    'foo: loop {
        let exponent = input();
        let m = 10u64.pow(exponent);
        let start: DateTime<Local> = Local::now();
        println!("{:?}", start.format("%a %e %b %T ").to_string());
        let beta = 0.00088;
        let alpha = beta * (exponent as f64 * 10.0_f64.ln()).powi(3);
        let n = (alpha * (m as f64).cbrt() + 0.5).floor() as usize;
        let z = (10.0_f64.powf(exponent as f64 * 2.0 / 3.0) / alpha).floor() as usize + 1;
        //if n > z { println!("adjust beta");
        //    return; }
        let mut ll = (n + 1) >> 1;
        if exponent <= 7 {
            ll = (m as usize -1) >> 1;
        }
        let mut mu: Vec<isize> = vec![1; ll + 2];
        let mut pi: Vec<usize> = vec![0; ll + 2];
        let pix = initialize_arrays(ll, &mut mu, &mut pi, &big_primes);
        // println!("mu = {:?}, pi = {:?}", mu,pi);
        if exponent <= 7 {
            println!("prime count = {} ", pix);
            let end: DateTime<Local> = Local::now();
            println!("{:?}", end - start);
            continue;
        }
        let a = pi[(n + 1) >> 1];
        let a_star = pi[(int_sqrt(n) + 1) >> 1];
        // println!("a_star = {:?}", a_star);
        let lc = (n as f64).log2().floor() as u8;
        let interval_length = (1 << lc) as usize;
        let last = interval_length - 1;
        let num_intervals = (z / interval_length) + 1;
        let mut m1: Vec<usize> = vec![n; a_star + 1];
        let mut phi: Vec<i64> = vec![0; a + 1];
        phi[0]=-1;
        let mut tt: Vec<u8> = vec![0; a - 1];
        let mut d2: Vec<usize> = vec![0; a - 1];
        let mut offsets: Vec<usize> = vec![0; a + 1];
        let mut interval_boundaries = (0..num_intervals).map(|i| i * interval_length)
            .collect::<Vec<usize>>();
        interval_boundaries.push(z);
        // println!("interval_boundaries {:?}", interval_boundaries);
        let mut u = match exponent % 2 {
            0 => 10i32.pow(exponent / 2) - 1,
            _ => 10.0_f64.powf(exponent as f64 / 2.0).floor() as i32,
        };
        if u % 2 == 0 {
            u -= 1;
        }
        let mut v = a;
        let mut count = a as i64 - 1 - ((a as i64 * (a as i64 - 1)) >> 1);
        count += ordinary_leaves(n, &mu, &m);
        let initial = (0..interval_length as i32)
            .map(|i| i + 1 & !i)
            .collect::<Vec<i32>>();
                    let mut p2primes;
        // start of main loop
        for interval in 0..num_intervals {
                let here: Intervals = (interval, &interval_boundaries, interval_length);
            let mut counter = initial.clone();
            for index in 0..=a {
                let pp = if index==a {0} else {big_primes[index+1] as u64};
                match index {
                    0 => {},
                    _ => {
                        let mut i = offsets[index];
                        while i < interval_length {
                            let mut pos = i;
                            if counter[pos] > 0 {
                                counter[pos] |= SIGNBIT;
                                while pos < interval_length {
                                    counter[pos] -= 1;
                                    pos |= pos + 1;
                                }
                            }
                            i += big_primes[index] as usize;
                        }
                        offsets[index] = i - interval_length  ;
                    },
                }
                let mut this: RegVars = (m, n, &mut count, &counter);
                if index < a_star {
                    special_leaves_type_1(index, here, this, &mut m1, pp as isize, &mu, &phi);
                }
                else if index < a - 1
                {
                    let mut s2b: S2bVars = (&mut d2[index], &pi, &big_primes);
                    if here.0 == 0b0 {
                        let term = (m  / (pp * pp )) as usize;
                        *s2b.0 = match term {
                            term if term <= pp as usize => index + 1,
                            term if term < n => pi[(term + 1) >> 1],
                            _ => a,
                        };
                        *this.2 += (a - *s2b.0) as i64;
                        special_leaves_type_2(index, here, &mut this, &mut s2b, &mut tt[index],pp);
                    }
                    let s2primes = special_leaves_type_2(index, here, &mut this, &mut s2b, &mut tt[index],pp);
                    *this.2 += s2primes * phi[index];
                }
                else if index == a {
                    let p2_var: P2Vars = (&mut u, v);
                    (p2primes,v) = p2(here, this, p2_var, &big_primes, a,);
                    count -= phi[index] * p2primes as i64;
                }
                phi[index] += (counter[last] & !SIGNBIT) as i64;
            }
        }
        //end of main loop
        count += (v as i64 * (v - 1) as i64) >> 1;
        println!("prime count for 10 ^ {} = {} ", exponent, count);
        let end: DateTime<Local> = Local::now();
        let elapsed = end - start;
        println!(
            "{} minutes {} seconds {} milliseconds",
            elapsed.num_minutes(),
            elapsed.num_seconds() - elapsed.num_minutes() * 60,
            elapsed.num_milliseconds() - elapsed.num_seconds() * 1000
        );
        continue 'foo;
    }
}
