extern crate bit_vec;
extern crate core;
extern crate itertools;
// extern crate chrono;
// extern crate mysilva_bin;
use bit_vec::BitVec;
use std::cmp;
use std::io;
// use std::cell::OnceCell;
use itertools::Itertools;
// use chrono::*;
const SIGNBIT: i32 = 1 << 31;
type Intervals<'a> = (usize, &'a [usize], usize);
type RegVars<'a> = (u64, usize, &'a mut i64, &'a [i32]);
type P2Vars<'a> = (&'a mut usize, usize, usize);
type S2bVars<'a> = (&'a mut usize, &'a [usize], &'a [usize]);

pub fn int_sqrt(n: usize) -> usize {
    ((n as f64).sqrt()).floor() as usize
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

// #[inline]
// pub fn cnt_update(mut pos : usize, counter : &mut[i32], last : usize ) {
//     counter[pos] |= SIGNBIT;
//     while pos <= last {
//       counter[pos] -= 1;
//       pos |= pos + 1;
//     }
//     }

#[inline]
pub fn interval_clear(
    j: usize,
    counter: &mut [i32],
    interval_length: usize,
    prime: usize,
) -> usize {
    // let last = interval_length - 1;
    (j..interval_length).step_by(prime).for_each(|mut i| {
        if counter[i] > 0 {
            counter[i] |= SIGNBIT;
            while i < interval_length {
                counter[i] -= 1;
                i |= i + 1;
            }
            // cnt_update( i, counter, last ) ;
        }
    }); // much slower ; no longer
        /*   for i in (j..interval_length).step_by(prime) {
         if counter[i] > 0 { cnt_update( i, counter, last) ; }
         }
        */
    /*
       match prime {
          2 =>
       }
    (prime - (interval_length - j) %prime) % prime
    */
 // no
    (j as i64 - interval_length as i64).rem_euclid(prime as i64) as usize // not sure why this works; yes, (interval - j) % prime = interval - i) % prime
}

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
            let term = (mu[(i + 1) >> 1]).signum() as i64;
            result += term * (*m as i64 / i as i64);
        } else {
            let term = (mu[((i >> 1) + 1) >> 1]).signum() as i64;
            result -= term * (*m as i64 / i as i64);
        }
    });
    result
}

//  pub fn rphi(term: i64,  mut a : usize, bit : i8 , primes: &[usize],  total : &mut i64 )  {
// 	loop {
// 		if a == 1 {
// 			*total +=  bit as i64 * term ;
// 			break;
// 			}
// 		else if term < primes[a] as i64 {
// 			*total += bit as i64 ;
// 			break;
// 				}
// 		else {
// 			a -= 1;
// 			rphi(term / (primes[a] as i64), a, -bit, primes, total) ;
// 					}
// 				}
// 		}

// pub fn special_leaves_type_1_substitute(b : usize, primes : &[usize], n : usize, mu : &[isize], m : u64) -> i64 {
//    let pp = primes[b + 1]    ; let mut acc = 0 ;
//    let mut j = cmp::max(n / pp , pp ) as usize + 1 ;
//    if j % 2 == 0 { j += 1;}
//    let mut i = j ; while i <= n {
//    //for i in (j..(n+1)).step_by(2) {
//    let muval1 = (mu[ ( i+1) >> 1 ] ).signum() ;
//    if (mu[(i + 1) >> 1]).abs() > pp as isize && muval1 != 0 {
//    let term = (m / (i * pp) as u64) as i64;
//    let mut total : i64 = 0;
//    rphi(term, b + 1, 1, primes, &mut total)  ;
//    acc += muval1 as i64 * total ;
//    }
//    i+=2 ; }
//    acc
//    }
/*#[inline]
pub fn s1b0(n: usize, mu: &[isize], m: u64) -> i64 {
    let mut acc = 0;
    let mut j = n / 2 +1;
    if j % 2 == 0 {
        j += 1;
    }
    for i in (j..=n).step_by(2) {
      let mui = mu[(i+1)>> 1];
        let muval1 = mui.signum();
        if mui.abs() > 2 
         {
            acc += muval1 as i64 * (m / (2 * i as u64)) as i64;
        }
    }
    acc
}*/
#[inline]
pub fn special_leaves_type_1(
    b: usize,
    intervals: Intervals,
    reg_var: RegVars,
    m1: &mut [usize],
    pp: usize,
    mu: &[isize],
    phi: &[u64],
) {
    // match b {0 => {if m1[b] % 2 == 0 {m1[b] -= 1}},
   /*  let mut start = reg_var.1 / pp + 1;
    if start % 2 == 0 {start +=1;}*/
   //  let m1b=m1[b];
    if (m1[b]) % 2 == 0 {
        m1[b] -= 1;
    }
    let criterion = reg_var.1 / pp;
    // if b==0 {phi[b] = intervals.2 as u64;}
    while m1[b] > criterion {// *pp > reg_var.1 {
        let y = (reg_var.0 / (m1[b] as u64 * pp as u64)) as usize ;
        if y >=intervals.1[intervals.0+1] {return;} 
      //   if y +1  < intervals.1[intervals.0] {return;}
        let muvalue = mu[(m1[b] + 1) >> 1];
        if muvalue.abs() > pp as isize {
            // println!("y = {} phi[0] = {} query = {}, sum of phi and query = {}",y,phi[b],query,phi[b] as i64+query) ;
            let query = cnt_query(y - intervals.1[intervals.0],reg_var.3) as i64;
            *reg_var.2 -= if b == 0 {muvalue.signum() as i64 * y as i64}
            else {
            muvalue.signum() as i64
                * (phi[b] as i64 + query)}; 
        }
        m1[b] -= 2;
      }
      }


#[inline]
pub fn hard(intervals: Intervals, reg_var: &mut RegVars, y: usize, d2_index: &mut usize) -> bool {
    (if y/* + 1*/ >= intervals.1[intervals.0 + 1] {
        return true;
    });
    *reg_var.2 += cnt_query(y /*+ 1*/ - intervals.1[intervals.0], reg_var.3) as i64;
    *d2_index -= 1;
    false
}

#[inline]
pub fn easy_sparse(
    index: usize,
    intervals: Intervals,
    reg_var: &mut RegVars,
    s2b_var: &mut S2bVars,
    y: usize,
    tt: &mut [u8],
    switch: &mut [bool],
) -> bool {
    if y < reg_var.1 {
        let l = s2b_var.1[(y + 1) >> 1] - index + 1;
        *reg_var.2 += l as i64;
        *s2b_var.0 -= 1;
    } else if !switch[index] {
        switch[index] = true;
        return true;
    } else {
        tt[index] = 2;
        hard(intervals, reg_var, y, s2b_var.0);
    }
    false
}

#[inline]
pub fn easy_clustered(
    index: usize,
    intervals: Intervals,
    reg_var: &mut RegVars,
    s2b_var: &mut S2bVars,
    y: usize,
    tt: &mut [u8],
    switch: &mut [bool],
) -> bool {
    if y < reg_var.1 {
        let l = s2b_var.1[(y + 1) >> 1] - index + 1;
        let term = reg_var.0 / (s2b_var.2[index + 1] as u64 * s2b_var.2[index + l] as u64);
        let dprime = s2b_var.1[((term + 1) >> 1) as usize];
        if s2b_var.2[dprime + 1] <= int_sqrt((reg_var.0 / s2b_var.2[index + 1] as u64) as usize)
            || dprime <= index
        {
            tt[index] = 1;
            *reg_var.2 += l as i64;
            *s2b_var.0 -= 1;
        } else {
            *reg_var.2 += (l as u32 * (*s2b_var.0 - dprime) as u32) as i64;
            *s2b_var.0 = dprime;
        }
    } else if !switch[index] {
        switch[index] = true;
        return true;
    } else {
        tt[index] = 2;
        hard(intervals, reg_var, y, s2b_var.0);
    }
    false
}

#[inline]
pub fn special_leaves_type_2(
    index: usize,
    intervals: Intervals,
    reg_var: &mut RegVars,
    s2b_var: &mut S2bVars,
    tt: &mut [u8],
    switch: &mut [bool],
) -> u32 {
    let mut s2bprimes = 0;
    while index + 1 < *s2b_var.0 {
        let y = (reg_var.0 / (s2b_var.2[index + 1] as u64 * s2b_var.2[*s2b_var.0] as u64)) as usize;
        match tt[index] {
            0 => {
                let easy_c: bool =
                    easy_clustered(index, intervals, reg_var, s2b_var, y, tt, switch);
                if easy_c {
                    break;
                }
            }
            1 => {
                let easy_s: bool = easy_sparse(index, intervals, reg_var, s2b_var, y, tt, switch);
                if easy_s {
                    break;
                }
            }
            _ => {
                let hard = hard(intervals, reg_var, y, s2b_var.0);
                if (intervals.0 > 0 || reg_var.3[1] > 0) && hard {
                    break;
                } else {
                    s2bprimes += 1;
                }
            }
        }
    }
    s2bprimes
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
    /* u : &mut usize, mut v : usize  ,mut  w : usize,*/ block: &mut BitVec,
    p: &[usize],
    a: usize,
) -> (u32, usize, usize) {
    // let mut v = a; let mut w = *u + 1;
    let mut p2primes = 0;
    loop {
        if *p2_var.0 <= reg_var.1 {
            *reg_var.2 += (p2_var.1 as i64 * (p2_var.1 - 1) as i64) >> 1;
            return (p2primes, p2_var.1, p2_var.2);
        }
        if *p2_var.0 < p2_var.2 {
            p2_var.2 = cmp::max(2, *p2_var.0 - reg_var.1);
            sieve2(p2_var.2, *p2_var.0 + 1, p, block);
        }
        if !block[*p2_var.0 - p2_var.2 + 1] {
            let y = (reg_var.0 / (*p2_var.0 as u64)) as usize;
            if y /*+1*/ >= intervals.1[intervals.0 + 1] {
                return (p2primes, p2_var.1, p2_var.2);
            }
            *reg_var.2 -=
                (cnt_query(y /*+ 1*/ - intervals.1[intervals.0], reg_var.3) as usize + a) as i64 - 1;
            p2primes += 1;
            p2_var.1 += 1;
        }
        *p2_var.0 -= 2;
    }
}
