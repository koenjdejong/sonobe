//! orders.rs — native data model + canonical flattening.
//!
//! The flattening order here MUST match the order your Noir `eval_commitment_poly`
//! Horner loop used, and the order the MPC uses to reconstruct phi, or the
//! fingerprint phi will not agree across the three views (ZKP / commitment / MPC).
//! Keep this function and the in-circuit RLC loop in lock-step.

use ark_ff::PrimeField;

// Match these to your Noir `constants` module. Kept small here for a light demo.
pub const MAX_ACTIONS: usize = 2;
pub const MAX_GOODS: usize = 2;

// Per-order field count, in canonical order. Must equal the in-circuit layout.
//   order.id, vehicle.id, vehicle.capacity            -> 3
//   per action: id, action_type, start, end, loc.id, lat, long -> 7
//   per good:   id, quantity, weight                  -> 3
pub const FIELDS_PER_ORDER: usize = 3 + 7 * MAX_ACTIONS + 3 * MAX_GOODS;

pub const ACTION_LOAD: u64 = 1;
pub const ACTION_UNLOAD: u64 = 2;
pub const ACTION_WAYPOINT: u64 = 3;

#[derive(Clone, Debug)]
pub struct Location { pub id: u64, pub longitude: u64, pub latitude: u64 }

#[derive(Clone, Debug)]
pub struct Action {
    pub id: u64,
    pub location: Location,
    pub start_time: u64,
    pub end_time: u64,
    pub action_type: u64,
}

#[derive(Clone, Debug)]
pub struct Good { pub id: u64, pub weight: u64, pub quantity: u64 }

#[derive(Clone, Debug)]
pub struct Vehicle { pub id: u64, pub capacity: u64 }

#[derive(Clone, Debug)]
pub struct TransportOrder {
    pub id: u64,
    pub vehicle: Vehicle,
    pub actions: [Action; MAX_ACTIONS],
    pub goods: [Good; MAX_GOODS],
}

impl TransportOrder {
    /// Canonical flattening: the exact sequence the RLC fingerprint consumes.
    pub fn flatten(&self) -> Vec<u64> {
        let mut v = Vec::with_capacity(FIELDS_PER_ORDER);
        v.push(self.id);
        v.push(self.vehicle.id);
        v.push(self.vehicle.capacity);
        for a in &self.actions {
            v.push(a.id);
            v.push(a.action_type);
            v.push(a.start_time);
            v.push(a.end_time);
            v.push(a.location.id);
            v.push(a.location.latitude);
            v.push(a.location.longitude);
        }
        for g in &self.goods {
            v.push(g.id);
            v.push(g.quantity);
            v.push(g.weight);
        }
        debug_assert_eq!(v.len(), FIELDS_PER_ORDER);
        v
    }

    pub fn flatten_field<F: PrimeField>(&self) -> Vec<F> {
        self.flatten().into_iter().map(F::from).collect()
    }
}

/// Generate `n` valid, non-overlapping orders, already sorted by (vehicle, start).
/// Sorted input is required for the adjacency check to mean anything; see the
/// permutation caveat in step_circuit.rs.
pub fn synthetic_orders(n: usize) -> Vec<TransportOrder> {
    let mut out = Vec::with_capacity(n);
    for i in 0..n {
        let base = (i as u64) * 10_000; // disjoint, monotone time windows
        let mk_action = |k: u64| Action {
            id: 1 + k,
            location: Location { id: 1, latitude: 52_241_327, longitude: 6_852_094 },
            start_time: base + k * 100,
            end_time: base + k * 100 + 50,
            action_type: ACTION_LOAD,
        };
        out.push(TransportOrder {
            id: (i as u64) + 1,
            vehicle: Vehicle { id: ((i as u64) % 5) + 1, capacity: 40_000_000 },
            actions: [mk_action(0), mk_action(1)],
            goods: [
                Good { id: 1, weight: 1_000_000, quantity: 10 },
                Good { id: 2, weight: 500_000, quantity: 5 },
            ],
        });
    }
    out
}
