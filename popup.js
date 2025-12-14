// popup.js - DealPal popup logic
document.addEventListener('DOMContentLoaded', () => {
  const scanBtn = document.getElementById('scanBtn');
  const trackedList = document.getElementById('trackedList');
  const lastSeen = document.getElementById('lastSeen');
  const consentCheckbox = document.getElementById('consent');

  // Load saved items
  chrome.storage.local.get(['trackedItems', 'consent'], (data) => {
    const items = data.trackedItems || [];
    consentCheckbox.checked = data.consent || false;
    displayItems(items);
  });

  scanBtn.addEventListener('click', () => {
    chrome.tabs.query({ active: true, currentWindow: true }, (tabs) => {
      if (!tabs[0]) return;
      chrome.scripting.executeScript(
        {
          target: { tabId: tabs[0].id },
          files: ['content-script.js']
        },
        () => {
          lastSeen.textContent = 'Scan executed.';
        }
      );
    });
  });

  consentCheckbox.addEventListener('change', () => {
    chrome.storage.local.set({ consent: consentCheckbox.checked });
  });

  // Listen for messages from content script
  chrome.runtime.onMessage.addListener((message) => {
    if (message.type === 'PRODUCT_INFO') {
      let items = [];
      chrome.storage.local.get('trackedItems', (data) => {
        items = data.trackedItems || [];
        const product = message.payload;
        // better price message
        const displayPrice = product.priceText ? product.priceText : 'Price not detected';
        product.displayPrice = displayPrice;

        items.unshift(product); // add newest on top
        chrome.storage.local.set({ trackedItems: items }, () => {
          displayItems(items);
        });
      });
    }
  });

  function displayItems(items) {
    trackedList.innerHTML = '';
    if (!items.length) {
      trackedList.innerHTML = '<div class="no-items">No tracked items yet.</div>';
      return;
    }
    items.forEach((product) => {
      const div = document.createElement('div');
      div.className = 'item';
      div.innerHTML = `<strong>${product.title}</strong><br>
                       Latest: ${product.displayPrice}<br>
                       <a href="${product.url}" target="_blank">View product</a>`;
      trackedList.appendChild(div);
    });
  }
});
