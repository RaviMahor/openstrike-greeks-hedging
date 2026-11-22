# OpenStrike: Dynamic Greeks Hedging & Options Execution Engine

[![Python 3.10+](https://img.shields.io/badge/python-3.10+-blue.svg)](https://www.python.org/downloads/)
[![Platform: Delta Exchange](https://img.shields.io/badge/Exchange-Delta%20Exchange-orange.svg)](https://www.delta.exchange)
[![Architecture: Greeks Hedging](https://img.shields.io/badge/Architecture-Delta--Neutral%20Hedging-green.svg)]()
[![Alerts: Telegram API](https://img.shields.io/badge/Alerts-Telegram%20Bot%20API-0088cc.svg)](https://core.telegram.org/bots)
[![Security: Zero Secrets](https://img.shields.io/badge/Security-Environment--Driven-brightgreen.svg)]()

A real-time systematic multi-leg options execution and dynamic Greeks risk management engine designed for **Delta Exchange** cryptocurrency options. Built to enforce delta-neutral stability, automated leg recovery, and disciplined contract expiry rolls.

---

## ⚡ Core Engine Features

1. **Portfolio Greeks Matrix**: Continuously calculates real-time Delta, Gamma, Vega, and Theta exposure across active options positions.
2. **3-Leg Equal Ratio Symmetry**: Maintains balanced delta-neutral hedge ratios across short and long strikes.
3. **Missing-Leg Auto-Recovery**: If a leg is stopped out, liquidated, or partially filled, the engine automatically detects the asymmetry and executes the missing leg to preserve hedge integrity.
4. **Automated Expiry Rolls**: Tracks time-to-settlement and initiates structured rolling sequences prior to expiry to eliminate gamma spikes.
5. **Interactive Telegram Remote Control**:
   - `mm <value>`: Instantly adjust margin allocation percentage remotely.
   - `snap`: Request live portfolio Greek snapshots to Telegram.
   - Emergency panic kill-switch (`k` in CLI, `/panic` via Telegram) to liquidate positions.

---

## 📊 Market Regime Suitability

| Market Condition | Suitability | Rationale |
| :--- | :--- | :--- |
| **Sideways to Moderately Volatile Channels** | **Optimal (USE)** | Allows steady theta decay extraction while dynamic delta rebalancing keeps risk contained. |
| **Extreme Overnight Price Gaps / Flash Freezes** | **Avoid (DO NOT USE)** | Orderbook slippage can impair rapid multi-leg rebalancing. |

---

## 🚀 Quickstart Guide

```bash
git clone https://github.com/RaviMahor/openstrike-greeks-hedging.git
cd openstrike-greeks-hedging

# Setup virtual environment
python3 -m venv venv
source venv/bin/activate
pip install -r requirements.txt

# Configure environment credentials
cp .env.example .env

# Run engine
python3 openstrike.py
```

---

## 👤 Author
**Ravi Mahor** · *Options & Derivatives Trader at Jainam Broking Limited*  
- **LinkedIn**: [linkedin.com/in/ravimahor](https://linkedin.com/in/ravimahor)  
- **Certifications**: NISM-Series-XVI (Commodity Derivatives) · NISM-Series-VIII (Equity Derivatives)
