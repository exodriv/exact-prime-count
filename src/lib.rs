use bit_vec::BitVec;
use std::cmp;
use std::io;
use itertools::Itertools;
const SIGNBIT: i32 = 1 << 31;
type Intervals<'a> = (usize, &'a [usize], usize);
type RegVars<'a> = (u64, usize, &'a mut i64, &'a [i32]);
type P2Vars<'a> = (&'a mut usize, usize, usize);
type S2bVars<'a> = (&'a mut usize, &'a [usize], &'a [usize]);

pub fn int_sqrt(n: usize) -> usize {
    (n as f64).sqrt().floor() as usize
}

#[inline]
pub fn cnt_query(mut pos: usize, counter: &[i32]) -> u32 {
    let mut acc = counter[pos] & !SIGNBIT;
    pos += 1;
    pos &= pos - 1;
    while pos != 0 {
        acc += counter[pos - 1] & !SIGNBIT;
        pos &= pos - 1;
    }
    acc as u32
}

/*#[inline]
pub fn interval_clear(
    j: usize,
    counter: &mut [i32],
    interval_length: usize,
    prime: usize,
) -> usize {
    (j..interval_length).step_by(prime).for_each(|i| {
        let mut pos = i;
        if counter[pos] > 0 {
            counter[pos] |= SIGNBIT;
            while pos < interval_length {
                counter[pos] -= 1;
                pos |= pos + 1;
            }
        }
    }
    );
    (j as i64 - interval_length as i64).rem_euclid(prime as i64) as usize
    // not sure why this works; yes, (interval - j) % prime = (interval - i) % prime
}
*/

pub fn input() -> u32 {
    println!("Please enter an integer from 1 to 18. The program will count the exact number of primes below this power of 10: ");
    let mut exponent = String::new();
    io::stdin()
        .read_line(&mut exponent)
        .expect("Failed to read line");
    let exponent: u32 = exponent.trim().parse().expect("Please enter an integer");
    match exponent {
        1..=18 => (),
        _ => {
            println!("Not a valid input: integer between 1 and 18");
            return 0;
        }
    }
    exponent
}

pub fn initialize_arrays(
    ll: usize,
    mu: &mut [isize],
    pi: &mut [usize],
    primes: &mut [usize],
) -> usize {
    for j in 2..mu.len() {
        if mu[j] == 1 {
            let mut i = j;
            while i <= ll {
                mu[i] = match mu[i] {
                    1 => 1 - 2 * j as isize,
                    _ => -mu[i],
                };
                i += 2 * j - 1;
            }
        }
    }
    let mut j = 2;
    while j * j <= ll << 1 {
        if mu[j] == 1 - 2 * j as isize {
            let mut i = 2 * j * j - 2 * j + 1;
            while i <= ll {
                mu[i] = 0;
                i += 4 * j * j - 4 * j + 1;
            }
        }
        j += 1;
    }
    primes[1] = 2;
    let mut pix = 1;
    for (i, elem) in mu.iter().enumerate().dropping(2) {
        if *elem == 1 - 2 * i as isize {
            pix += 1;
            primes[pix] = 2 * i - 1;
        }
        pi[i] = pix;
    }
    //println!("{:?}",mu) ;
    pix
}

pub fn ordinary_leaves(n: usize, mu: &[isize], m: &u64) -> i64 {
    let mut result = 0;
    let it = (1..n + 1).filter(|&i| i % 4 != 0);
    it.for_each(|i| {
        if i % 2 == 1 {
            let term = mu[(i + 1) >> 1].signum() as i64;
            result += term * (*m as i64 / i as i64);
        } else {
            let term = mu[((i >> 1) + 1) >> 1].signum() as i64;
            result -= term * (*m as i64 / i as i64);
        }
    });
    result
}

#[inline]
pub fn special_leaves_type_1(b: usize, intervals: Intervals, reg_var: RegVars, m1: &mut [usize], pp: usize, mu: &[isize], phi: &[i64],) {
    // println!("b= {}, phi = {:?}",b,phi);
    if (m1[b]) % 2 == 0 {
        m1[b] -= 1;
    }
    let criterion = reg_var.1 / pp;
            let fudge: i64 = if b == 0 { 1 } else { 0 };
    let mut y; 
    let mut mu_value ;
    let mut query;
    while m1[b] > criterion {
         y = (reg_var.0 / (m1[b] as u64 * pp as u64)) as usize;
         mu_value = mu[(m1[b] + 1) >> 1];
        if /*mu_value.abs() >*/ pp < mu_value.abs() as usize {
        if y >= intervals.1[intervals.0 + 1] { return; } else {
            query = cnt_query(y - intervals.1[intervals.0], reg_var.3) as i64;
            *reg_var.2 -= mu_value.signum() as i64 * (phi[b] + query - fudge);
        }
    }
        m1[b] -= 2;
      }
      }

#[inline]
pub fn special_leaves_type_2(index: usize, intervals: Intervals, reg_var: &mut RegVars, s2b_var: &mut S2bVars, tt_index: &mut u8,pp:u64) -> i64 {
    let mut s2_primes = 0;
let term2 = int_sqrt((reg_var.0/pp) as usize);
    while *s2b_var.0   > index + 1 {
        let mut y = (reg_var.0 / (pp * s2b_var.2[*s2b_var.0] as u64)) as usize;
        let bit_n = y < reg_var.1;
        match tt_index {
            0 => {
                if bit_n {
                    let l = s2b_var.1[(y + 1) >> 1] - index + 1;
                    let term = reg_var.0/(pp * s2b_var.2[index + l] as u64);
                    let d_prime = s2b_var.1[((term + 1) >> 1) as usize];
                    if s2b_var.2[d_prime + 1] <= term2 // int_sqrt((reg_var.0 /pp /*s2b_var.2[index + 1] as u64*/) as usize)
                        || d_prime <= index
                    {
                        *tt_index = 1;
                        *reg_var.2 += l as i64;
                        *s2b_var.0 -= 1;
                    } else {
                        *reg_var.2 += (l as u32 * (*s2b_var.0 - d_prime) as u32) as i64;
                        *s2b_var.0 = d_prime;
                    }
                } else {
                    // *tt_index = 2u8;
                    return s2_primes;
                    // break;
                }
            },
            1 => {
                if bit_n {
                    let l = s2b_var.1[(y + 1) >> 1] - index + 1;
                    *reg_var.2 += l as i64;
                    *s2b_var.0 -= 1;
                } else {
                    *tt_index = 2;
                    return s2_primes;
                    // break;
                }
            },
            _ => {
             y -= intervals.1[intervals.0];
            if y < intervals.2
                {
                    *reg_var.2 += cnt_query(y, reg_var.3) as i64;
                    *s2b_var.0 -= 1;
                    s2_primes += 1;
                }
            else {
                return s2_primes;
            // break;
            }
        },
        }
}
    s2_primes
}

#[inline]
pub fn sieve2(x: usize, y: usize, p: &[usize], block: &mut BitVec) {
    block.clear();
    let mut i = 1;
    while p[i] * p[i] <= y {
        let mut offset = (1 - x as i64).rem_euclid(p[i] as i64) as usize;
        //    (offset..2+y-x).step(p[i]).foreach(|j| block.set(j,true) ) ;// more than twice the time - map/collect makes no difference
        while offset <= 1 + (y - x) {
            block.set(offset, true);
            offset += p[i];
        }
        i += 1;
    }
}

#[inline]
pub fn p2(
    intervals: Intervals,
    reg_var: RegVars,
    mut p2_var: P2Vars,
    block: &mut BitVec,
    p: &[usize],
    a: usize,
) -> (u32, usize, usize) {
    let mut p2primes = 0;
    while *p2_var.0 > reg_var.1 {
        if *p2_var.0 < p2_var.2 {
            p2_var.2 = cmp::max(2, *p2_var.0 - reg_var.1);
            sieve2(p2_var.2, *p2_var.0 + 1, p, block);
        }
        if !block[*p2_var.0 - p2_var.2 + 1] {
            let y = (reg_var.0 / (*p2_var.0 as u64)) as usize;
           if y < intervals.1[intervals.0 + 1] {
            *reg_var.2 -=
                (cnt_query(y - intervals.1[intervals.0], reg_var.3) as usize + a) as i64 - 1;
            p2primes += 1;
            p2_var.1 += 1;
        } else {
              break;
           }
        }
        *p2_var.0 -= 2;
}
     (p2primes, p2_var.1, p2_var.2)
}
