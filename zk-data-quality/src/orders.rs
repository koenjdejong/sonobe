use crate::otm::{ACTION_LOAD, Action, Good, Location, TransportOrder, Vehicle};


pub fn synthetic_orders(n: usize) -> Vec<TransportOrder> {
    let mut out = Vec::with_capacity(n);
    for i in 0..n {
        let base = (i as u64) * 10_000; // disjoint, monotone time windows
        let mk_action = |k: u64| Action {
            id: 1 + k,
            active: true,
            location: Location { id: 1, latitude: 52_241_327, longitude: 6_852_094 },
            start_time: base + k * 100,
            end_time: base + k * 100 + 50,
            action_type: ACTION_LOAD,
        };
        out.push(TransportOrder {
            id: (i as u64) + 1,
            active: true,
            vehicle: Vehicle { id: ((i as u64) % 5) + 1, capacity: 40_000_000 },
            actions: [mk_action(0), mk_action(1), mk_action(2), mk_action(3), mk_action(4), mk_action(5), mk_action(6), mk_action(7)],
            goods: [
                Good { id: 1, active: true, weight: 1_000_000, quantity: 10 },
                Good { id: 2, active: true, weight: 500_000, quantity: 5 },
                Good { id: 3, active: true, weight: 250_000, quantity: 2 },
                Good { id: 4, active: true, weight: 100_000, quantity: 1 },
                Good { id: 5, active: true, weight: 50_000, quantity: 1 },
                Good { id: 6, active: true, weight: 25_000, quantity: 1 },
                Good { id: 7, active: true, weight: 10_000, quantity: 1 },
                Good { id: 8, active: true, weight: 5_000, quantity: 1 },
            ],
        });
    }
    out
}
