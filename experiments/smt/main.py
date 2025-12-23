import matplotlib.pyplot as plt

# Data transcribed from the table
years = list(range(2011, 2026))

submitted = [
    141,  # 2011
     83,  # 2012
     99,  # 2013
     83,  # 2014
    108,  # 2015
     70,  # 2016
     77,  # 2017
     92,  # 2018
     72,  # 2019
     62,  # 2020
     60,  # 2021
    118,  # 2022
     75,  # 2023
     68,  # 2024
     65,  # 2025
]

acceptance_rate = [
    27.00,  # 2011
    38.70,  # 2012
    37.30,  # 2013
    35.00,  # 2014
    30.60,  # 2015
    41.42,  # 2016
    40.25,  # 2017
    33.69,  # 2018
    39.00,  # 2019
    40.13,  # 2020
    36.36,  # 2021
    30.05,  # 2022
    38.05,  # 2023
    38.00,  # 2024
    36.92,  # 2025
]

# -----------------------------
# Visualization
# -----------------------------
plt.figure()
plt.plot(years, submitted, label='Submitted Papers')
plt.plot(years, acceptance_rate, label='Acceptance Rate (%)')
plt.xlabel("Year")
plt.ylabel("Value")
plt.title("Submitted Papers and Acceptance Rate per Year")
plt.legend()
plt.savefig('experiments/smt/plot.png', dpi=150, bbox_inches='tight')
print("Plot saved to experiments/smt/plot.png")

# -----------------------------
# Averages for last 5 years
# -----------------------------
last_5_submitted = submitted[-5:]
last_5_acceptance = acceptance_rate[-5:]

avg_submitted = sum(last_5_submitted) / len(last_5_submitted)
avg_acceptance = sum(last_5_acceptance) / len(last_5_acceptance)

print(f"Average submissions (last 5 years): {avg_submitted:.1f}")
print(f"Average acceptance rate (last 5 years): {avg_acceptance:.2f}%")
