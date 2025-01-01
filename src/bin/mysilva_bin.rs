extern crate mysilva;
// extern crate chrono ;
extern crate bit_vec;
extern crate itertools;
// use std::io;
// use std::cell::OnceCell;
use bit_vec::BitVec;
use chrono::*;
use mysilva::*;
// use itertools::Itertools ;
const SIGNBIT: i32 = 1 << 31;
type Intervals<'a> = (usize, &'a [usize], usize);
type RegVars<'a> = (u64, usize, &'a mut i64, &'a [i32]);
type P2Vars<'a> = (&'a mut usize, usize, usize);
type S2bVars<'a> = (&'a mut usize, &'a [usize], &'a [usize]);
fn main() {
    'foo: loop {
        // let cell: OnceCell<u64> = OnceCell::new();
        let exponent = input();
        let m = 10u64.pow(exponent);
        let start: DateTime<Local> = Local::now();
        println!("{:?}", start.format("%a %e %b %T ").to_string());
        let beta = 0.00085;
        let alpha = beta * (exponent as f64 * 10.0_f64.ln()).powi(3);
        let n = (alpha * (m as f64).cbrt() + 0.5).floor() as usize;
        let z = (10.0_f64.powf(exponent as f64 * 2.0 / 3.0) / alpha).floor() as usize + 1;
        //if n > z { println!("adjust beta");
        //    return; }
        let mut ll = (n + 1) >> 1;
        if exponent <= 7 {
            ll = (m as usize - 1) >> 1;
        }
        let mut primes: Vec<usize> = vec![1; ll + 1];
        let mut mu: Vec<isize> = vec![1; ll + 1];
        let mut pi: Vec<usize> = vec![0; ll + 1];
        let pix = initialize_arrays(ll, &mut mu, &mut pi, &mut primes);
        if exponent <= 7 {
            println!("prime count = {} ", pix);
            let end: DateTime<Local> = Local::now();
            println!("{:?}", end - start);
            continue;
        }
        primes.truncate(pix + 1);
        let a = pi[(n + 1) >> 1];
        let astar = pi[(int_sqrt(n) + 1) >> 1];
        let lc = (n as f64).log2().floor() as u8;
        let interval_length = (1 << lc) as usize;
        let last = interval_length - 1;
        let num_intervals = (z / interval_length) + 1;
        let mut interval_boundaries: Vec<usize> = vec![0; num_intervals + 1];
        let mut initial: Vec<i32> = vec![0; interval_length];
        let mut m1: Vec<usize> = vec![n; astar + 1];
        let mut phi: Vec<u64> = vec![0; a + 1];
        let mut tt: Vec<u8> = vec![0; a - 1];
        let mut d2: Vec<usize> = vec![0; a - 1];
        let mut offsets: Vec<usize> = vec![0; a + 1];
        let mut block: BitVec = BitVec::from_elem(n + 3, false);
        let mut switch: Vec<bool> = vec![false; a + 1];
        (1..num_intervals).for_each(|i| interval_boundaries[i] = i * interval_length);
        interval_boundaries[num_intervals] = z;
        let mut u = match exponent % 2 {
            0 => 10usize.pow(exponent / 2) - 1,
            _ => 10.0_f64.powf(exponent as f64 / 2.0).floor() as usize,
        };
        if u % 2 == 0 {
            u -= 1;
        }
        let mut v = a;
        let mut w = u + 1;
        let mut count = a as i64 - 1 - ((a as i64 * (a as i64 - 1)) >> 1);
        count += ordinary_leaves(n, &mu, &m);
        // count -= s1b0(n, &mu, m);
        (astar..a - 1).for_each(|index| {
            {
                let pp = primes[index + 1];
                let term = (m / (pp as u64 * pp as u64)) as usize;
                d2[index] = match term {
                    term if term <= pp => index + 1,
                    term if term < n => pi[(term + 1) >> 1],
                    _ => a,
                };
                count += (a - d2[index]) as i64;
            };
        });
        let temp = vec![0; interval_length];
        initial
            .iter_mut()
            .enumerate()
            .for_each(|(i, e)| *e = (i as i32 + 1) & !(i as i32));
        // start of main loop
        for interval in 0..num_intervals {
            let counter = &mut initial.clone();
            for index in 0..a + 1 {
                match index {
                    0 => {},
                    _ => {
                        offsets[index] =
                            interval_clear(offsets[index], counter, interval_length, primes[index]);
                    },
                }
                let here: Intervals = (interval, &interval_boundaries, interval_length);
                let mut this: RegVars = (m, n, &mut count, counter);
                if index < astar {
                    special_leaves_type_1(index, here, this, &mut m1, primes[index + 1], &mu, &phi);
                }
                else if index < a - 1
                {
                    let mut s2b: S2bVars = (&mut d2[index], &pi, &primes);
                    if here.0 == 0b0 {
                        this.3 = &temp;
                        special_leaves_type_2(
                            index,
                            here,
                            &mut this,
                            &mut s2b,
                            &mut tt,
                            &mut switch,
                        );
                    }
                    this.3 = counter;
                    let s2primes = special_leaves_type_2(
                        index,
                        here,
                        &mut this,
                        &mut s2b,
                        &mut tt,
                        &mut switch,
                    );
                    count += (s2primes as u64 * phi[index]) as i64;
                } else if !switch[index] && index < a - 1 {
                    continue;
                } else if index == a {
                    let p2_var: P2Vars = (&mut u, v, w);
                    let p2return = p2(
                        here, this, p2_var, /*&mut u, v, w,*/ &mut block, &primes, a,
                    );
                    let p2primes = p2return.0;
                    (_, v, w) = p2return;
                    count -= phi[index] as i64 * p2primes as i64;
                }
                phi[index] += (counter[last] & !SIGNBIT) as u64;
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
